extern crate bitcoin;
extern crate dlc;
extern crate dlc_trie;
extern crate rust_decimal;
extern crate rust_decimal_macros;
extern crate secp256k1_zkp;

use std::collections::HashMap;

use bitcoin::{Address, Network, OutPoint, Script};
use dlc::{
    secp_utils::schnorrsig_decompose, OracleInfo, PartyParams, Payout, RangePayout, TxInputInfo,
};
use dlc_trie::{multi_oracle_trie::MultiOracleTrie, DlcTrie, OracleNumericInfo};
use rust_decimal::prelude::*;
use secp256k1_zkp::{
    bitcoin_hashes::sha256::Hash as Sha256,
    rand::{rngs::ThreadRng, RngCore},
    schnorrsig::{
        KeyPair as SchnorrKeyPair, PublicKey as SchnorrPublicKey, Signature as SchnorrSignature,
    },
    All, Message, PublicKey, Secp256k1, SecretKey,
};

const DESIRED_ATTESTATION_OUTCOME: usize = 10;
const NB_ORACLES: usize = 3;
const THRESHOLD: usize = 2; // Change this to 3 and watch it fail

fn generate_new_address(secp: &Secp256k1<All>, rng: &mut ThreadRng) -> Script {
    let sk = bitcoin::PrivateKey {
        key: SecretKey::new(rng),
        network: Network::Testnet,
        compressed: true,
    };
    let pk = bitcoin::PublicKey::from_private_key(secp, &sk);
    Address::p2wpkh(&pk, Network::Testnet)
        .unwrap()
        .script_pubkey()
}

fn create_counterparty(
    secp: &Secp256k1<All>,
    rng: &mut ThreadRng,
    input_amount: u64,
    collateral: u64,
    id: u64,
) -> (PartyParams, SecretKey) {
    // input_amount is the amount of bitcoin that the party's inputs amount to
    // collateral is the amount of bitcoin that will be going into the contract
    // (input_amount - collateral) will be given back in the funding transaction as
    // change

    let secret_key = SecretKey::new(rng);
    let public_key = PublicKey::from_secret_key(&secp, &secret_key);

    // specify where to send change and where to send the final payout for this party
    let change_script_pubkey = generate_new_address(secp, rng);
    let payout_script_pubkey = generate_new_address(secp, rng);

    // specify information about the inputs for this lender, it is possible that there will
    // be several of these inputs for each party which is why you should specify a `serial_id` for
    // each input for ordering purposes in the final transaction. because this tutorial assumes
    // only one input for each party, we can trivially set this as so
    // max_witness_len describes the maximum length of a witness required to spend this outpoint.
    // this is for the purpose of calculating fees
    let input = TxInputInfo {
        outpoint: OutPoint::null(),
        max_witness_len: 108,
        redeem_script: Script::new(),
        serial_id: id,
    };

    let params = PartyParams {
        fund_pubkey: public_key,

        input_amount,
        collateral,

        change_script_pubkey,
        change_serial_id: id,

        payout_script_pubkey,
        payout_serial_id: id,

        inputs: vec![input],
    };

    (params, secret_key)
}

struct OracleSecret {
    sk_nonces: Vec<[u8; 32]>,
    kp: SchnorrKeyPair,
}

fn get_oracles_details(
    secp: &Secp256k1<All>,
    rng: &mut ThreadRng,
    nb_digits: usize,
    nb_oracles: usize,
) -> Vec<(OracleInfo, OracleSecret)> {
    // in reality you don't get to dictate the number of digits the oracle attests to but FID!
    (0..nb_oracles)
        .map(|_| {
            let (oracle_kp, oracle_pubkey) = secp.generate_schnorrsig_keypair(rng);

            let n = (0..nb_digits)
                .map(|_| {
                    let mut sk_nonce = [0u8; 32];
                    rng.fill_bytes(&mut sk_nonce);

                    let oracle_r_kp = SchnorrKeyPair::from_seckey_slice(secp, &sk_nonce).unwrap();
                    let nonce = SchnorrPublicKey::from_keypair(secp, &oracle_r_kp);

                    (sk_nonce, nonce)
                })
                .collect::<Vec<_>>();

            let sk_nonces = n.iter().map(|x| x.0).collect::<Vec<_>>();
            let nonces = n.iter().map(|x| x.1).collect::<Vec<_>>();

            let oracle_info = OracleInfo {
                public_key: oracle_pubkey,
                nonces,
            };

            let oracle_secret = OracleSecret {
                sk_nonces,
                kp: oracle_kp,
            };

            (oracle_info, oracle_secret)
        })
        .collect()
}

fn generate_precomputed_points(
    secp: &Secp256k1<All>,
    oracle_details: &[OracleInfo],
) -> Vec<Vec<Vec<PublicKey>>> {
    oracle_details
        .iter()
        .map(|dets| {
            let pubkey = dets.public_key;
            let nonces = &dets.nonces;
            nonces
                .iter()
                .map(|nonce| {
                    (0u8..=1)
                        .map(|outcome| {
                            let message = Message::from_hashed_data::<Sha256>(&[outcome]);
                            dlc::secp_utils::schnorrsig_compute_sig_point(
                                secp, &pubkey, nonce, &message,
                            )
                            .unwrap()
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
}

fn signatures_to_secret(signatures: &[SchnorrSignature]) -> SecretKey {
    let s_values = signatures
        .iter()
        .map(|sig| schnorrsig_decompose(sig).unwrap().1)
        .collect::<Vec<_>>();
    let mut secret = SecretKey::from_slice(s_values[0]).unwrap();
    for s in s_values.iter().skip(1) {
        secret.add_assign(s).unwrap()
    }
    secret
}

struct OracleAttestation {
    outcome: usize,
    // the schnorr signature for each digit
    signatures: Vec<SchnorrSignature>,
}

fn retrieve_oracle_attestations(
    secp: &Secp256k1<All>,
    oracles_secrets: &[OracleSecret],
    // messages: &[Vec<Vec<Message>>],
) -> HashMap<usize, OracleAttestation> {
    // this function returns a hash map that maps an oracle index to the attestation associated
    // with such oracle index. the oracle index is the index by which its details was passed into
    // the trie functions in the precomputed points 3d vector

    let messages = (0..1) // n_outcomes
        .map(|x| {
            (0..NB_ORACLES) // n_oracles
                .map(|y| {
                    (0..18) // n_digits
                        .map(|z| {
                            // println!("{}", ((y + x + z) as u8));
                            Message::from_hashed_data::<Sha256>(&[((y + x + z) as u8)])
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    // return any number of oracle attestations so long as the number we return is bigger than the
    // THRESHOLD
    // let oracle_indices = [0, 1, 2]; // Actually this should be equal to or greater than the THRESHOLD right? why bigger?
    let oracle_indices: Vec<usize> = (0..NB_ORACLES).collect();

    let mut map = HashMap::new();

    for &i in oracle_indices.iter() {
        let mut signatures = vec![];
        for j in 0..18 {
            let oracle_kp = &oracles_secrets[i].kp;
            let oracle_sk_nonce = &oracles_secrets[i].sk_nonces[j];
            // println!("{:?}", messages[0][i][j]);
            let sig = dlc::secp_utils::schnorrsig_sign_with_nonce(
                &secp,
                &messages[0][i][j], // we are choosing 0 as our digit for every digit, effectively attesting to bitcoin at 0 // What? no it doesn't seem you are chosing 0...
                oracle_kp,
                oracle_sk_nonce,
            );
            signatures.push(sig);
        }
        let attestation = OracleAttestation {
            outcome: DESIRED_ATTESTATION_OUTCOME + (i % THRESHOLD), // RIP
            signatures,
        };
        map.insert(i, attestation);
    }

    map
}

fn main() {
    println!("begin");
    let secp = Secp256k1::new();
    let mut rng = secp256k1_zkp::rand::thread_rng();

    let blockchain = MockBlockchain::new();

    let party_collateral = 50_000;

    // generate our two parties
    let alice = create_counterparty(&secp, &mut rng, 100_000_000, party_collateral, 0);
    let bob = create_counterparty(&secp, &mut rng, 75_000, party_collateral, 1);

    // decontruct our two parties
    let (alice_params, alice_secret) = alice;
    let (bob_params, bob_secret) = bob;

    let nb_digits = 18;
    // let NB_ORACLES = 3; // we are using five oracles
    // let THRESHOLD = 3; // we need three of the five oracles to agree

    // all of our oracles are going to attest in base 2 and assume that all of them attest to the
    // same number of digits (i.e. 18 in this example). You could manage oracles that attested to
    // different number of digits
    // This variable's nb_digits holds a vec of each oracles nb_digits to sign.
    let oracle_numeric_infos = OracleNumericInfo {
        base: 2,
        nb_digits: vec![nb_digits; NB_ORACLES],
    };

    // we can use this trie to efficiently create adaptor signatures, verify adaptor signatures and
    // create transaction signatures from adaptor signatures for numeric dlcs
    let mut trie = MultiOracleTrie::new(&oracle_numeric_infos, THRESHOLD).unwrap();

    // again we will only show the example where alice signs adaptor signatures for bob and not the
    // other way around

    let oracles = get_oracles_details(&secp, &mut rng, nb_digits, NB_ORACLES);
    let oracles_infos = oracles.iter().map(|o| o.0.clone()).collect::<Vec<_>>();
    let oracles_secrets = oracles.into_iter().map(|o| o.1).collect::<Vec<_>>();

    // let (oracle_info, oracle_secret) = get_oracle_details(&secp, &mut rng);

    // denote alice and bob as offerer and accepter respectively
    // alice is betting on unc winning and bob is betting on duke winning

    let incremental_payout = (party_collateral as usize * 2) / 100;
    let mut range_payouts = vec![];
    for n in 0..=100 {
        range_payouts.push(RangePayout {
            start: n,
            count: 1,
            payout: Payout {
                offer: (n * incremental_payout).to_u64().unwrap(),
                accept: ((100 - n) * incremental_payout).to_u64().unwrap(),
            },
        });
    }

    let payouts = range_payouts
        .iter()
        .map(|rp| rp.payout.clone())
        .collect::<Vec<_>>();

    let refund_lock_time = 100;
    let fee_rate_per_vb = 4;
    let fund_lock_time = 10;
    let cet_lock_time = 10;
    let fund_output_serial_id = 0;

    let dlc_transactions = dlc::create_dlc_transactions(
        &alice_params,
        &bob_params,
        &payouts,
        refund_lock_time,
        fee_rate_per_vb,
        fund_lock_time,
        cet_lock_time,
        fund_output_serial_id,
    )
    .expect("error generating dlc transactions");

    // ---multi stuff starting here---
    let funding_transaction = dlc_transactions.fund;
    let cets = dlc_transactions.cets;
    let funding_script_pubkey = dlc_transactions.funding_script_pubkey;
    let _refund_transaction = dlc_transactions.refund;
    let fund_output_value = funding_transaction.output[0].value;
    // the trie needs information about the oracles to construct the trie that will dictate
    // creation of adaptor signatures. make this super high dimensional table that will "store" the
    // oracle public information. almost all of the tables have similar forms just i would just
    // learn how to construct it and not really how it is used
    let precomputed_points = generate_precomputed_points(&secp, &oracles_infos);

    let alice_adaptor_sigs = trie
        .generate_sign(
            &secp,
            &alice_secret,
            &funding_script_pubkey,
            fund_output_value,
            &range_payouts,
            &cets,
            &precomputed_points,
            0, // this value is not incredibly important to worry about
        )
        .unwrap();

    // bob can now verify alice's adaptor signatures
    trie.verify(
        &secp,
        &alice_params.fund_pubkey,
        &funding_script_pubkey,
        fund_output_value,
        &alice_adaptor_sigs,
        &cets,
        &precomputed_points,
    )
    .expect("invalid adaptor signatures");
    println!("Adaptor sigs in the trie are verified!");

    // Iterate over the trie tree
    // for i in trie.iter() {
    //     println!("{:?}", i);
    // }

    // everything is good! broadcast the funding transaction
    println!("Broadcasting the DLC to the chain!");
    blockchain.broadcast(&funding_transaction);
    println!("Success!");

    let attestations = retrieve_oracle_attestations(&secp, &oracles_secrets);

    // for each attestation, convert the price of bitcoin into binary representation. this enables
    // the trie to lookup which information to find that would be relevant
    let mut paths = attestations
        .iter()
        .map(|(&oracle_index, attestation)| {
            let mut x = attestation.outcome;
            let path = (0..nb_digits)
                .map(|_| {
                    let blah = x % 2;
                    x >>= 1;
                    blah
                })
                .collect::<Vec<_>>()
                .iter()
                .rev()
                .cloned()
                .collect();
            (oracle_index, path)
        })
        .collect::<Vec<_>>();

    paths.sort(); // This sort ensures that we get the oracle with index 0 first, then 1, etc...

    println!(
        "Searching for the trie entry for the following attestation tuple: {:?}",
        paths
    );

    // range info will tell us which adaptor signature and cet to use
    let (range_info, indexed_paths) = trie
        .look_up(&paths)
        .expect("Expected the outcomes to exist in the sig trie tree");

    println!("Found!");

    println!("Indexed paths {:?}", indexed_paths);
    println!("Range info {:?}", range_info);

    // extract the signatures from the trie based on the indexed paths from above
    let all_sigs = indexed_paths
        .iter()
        .flat_map(|(oracle_index, outcome_digits)| {
            let sigs = &attestations.get(oracle_index).unwrap().signatures;
            let outcome_digits = outcome_digits.iter().collect::<Vec<_>>(); // this seems to do nothing useful
                                                                            // for x in sigs.iter().enumerate() {
                                                                            //     println!(
                                                                            //         "Oracle: {}: sig digit: {:?} ----- sig: {:?}",
                                                                            //         oracle_index, x.0, x.1
                                                                            //     );
                                                                            // }
                                                                            // The outcome digits seem odd, they go from 0-17, rather than being the binary digits signed. Which seems odd to me. Why would the oracle have signed the digits above 1?
            sigs.iter()
                .enumerate()
                .filter(|(i, _)| outcome_digits.contains(&i))
                .map(|(_, sig)| sig)
                .collect::<Vec<_>>()
        })
        .cloned()
        .collect::<Vec<_>>();

    // compress all of the signatures into one secret key that can be used to decrypt the adaptor
    // signature
    let adaptor_dec_key = signatures_to_secret(&all_sigs);

    let valid_adaptor_sig = alice_adaptor_sigs[range_info.adaptor_index];
    let alice_signature = valid_adaptor_sig.decrypt(&adaptor_dec_key).unwrap();

    let mut valid_cet = cets[range_info.cet_index].clone();

    dlc::util::sign_multi_sig_input(
        &secp,
        &mut valid_cet,
        &alice_signature,
        &alice_params.fund_pubkey,
        &bob_secret,
        &funding_script_pubkey,
        fund_output_value,
        0, // input_index that this is signing multisig for
    );

    println!("Putting the close transaction on chain");
    blockchain.broadcast(&valid_cet);
    println!("Success!");

    // if something bad were to happen (e.g. oracle does not attest to event), then alice and bob
    // can get their collateral back with the refund transaction
    // blockchain.broadcast(&dlc_transactions.refund);

    println!("finished");
}

use bitcoin::Transaction;

struct MockBlockchain {}

impl MockBlockchain {
    fn new() -> MockBlockchain {
        MockBlockchain {}
    }

    fn broadcast(&self, _transaction: &Transaction) {
        // this isn't actually a blockchain! i wonder if they fell for it
    }
}
