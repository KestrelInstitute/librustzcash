extern crate bellman;
extern crate blake2_rfc;
extern crate byteorder;
extern crate libc;
extern crate pairing;
extern crate rand;
extern crate sapling_crypto;
extern crate zcash_primitives;
extern crate zcash_proofs;

extern crate lazy_static;

use pairing::{
    bls12_381::{Bls12, Fr, FrRepr},
    BitIterator, PrimeField, PrimeFieldRepr,
};

use sapling_crypto::{
    circuit::multipack,
    constants::CRH_IVK_PERSONALIZATION,
    jubjub::{
        edwards,
        fs::{Fs, FsRepr},
        FixedGenerators, JubjubEngine, JubjubParams, PrimeOrder, ToUniform, Unknown,
    },
    pedersen_hash::{pedersen_hash, Personalization},
    redjubjub::{self, Signature},
};

use sapling_crypto::circuit::sapling::TREE_DEPTH as SAPLING_TREE_DEPTH;
use sapling_crypto::circuit::sprout::{self, TREE_DEPTH as SPROUT_TREE_DEPTH};

use bellman::groth16::{
    create_random_proof, verify_proof, Parameters, PreparedVerifyingKey, Proof,
};

use blake2_rfc::blake2s::Blake2s;

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

use rand::{OsRng, Rng};
use std::io::BufReader;

use libc::{c_char, c_uchar, int64_t, size_t, uint32_t, uint64_t};
use std::ffi::CStr;
use std::fs::File;
use std::slice;

use sapling_crypto::primitives::{ProofGenerationKey, ViewingKey};
use zcash_primitives::{sapling::spend_sig, JUBJUB};
use zcash_proofs::{
    load_parameters,
    sapling::{CommitmentTreeWitness, SaplingProvingContext},
};

pub mod equihash;
pub mod sapling;

use sapling::SaplingVerificationContext;

#[cfg(test)]
mod tests;

static mut SAPLING_SPEND_VK: Option<PreparedVerifyingKey<Bls12>> = None;
static mut SAPLING_OUTPUT_VK: Option<PreparedVerifyingKey<Bls12>> = None;
static mut SPROUT_GROTH16_VK: Option<PreparedVerifyingKey<Bls12>> = None;

static mut SAPLING_SPEND_PARAMS: Option<Parameters<Bls12>> = None;
static mut SAPLING_OUTPUT_PARAMS: Option<Parameters<Bls12>> = None;
static mut SPROUT_GROTH16_PARAMS_PATH: Option<String> = None;

fn is_small_order<Order>(p: &edwards::Point<Bls12, Order>) -> bool {
    p.double(&JUBJUB).double(&JUBJUB).double(&JUBJUB) == edwards::Point::zero()
}

/// Writes an FrRepr to [u8] of length 32
fn write_le(f: FrRepr, to: &mut [u8]) {
    assert_eq!(to.len(), 32);

    f.write_le(to).expect("length is 32 bytes");
}

/// Reads an FrRepr from a [u8] of length 32.
/// This will panic (abort) if length provided is
/// not correct.
fn read_le(from: &[u8]) -> FrRepr {
    assert_eq!(from.len(), 32);

    let mut f = FrRepr::default();
    f.read_le(from).expect("length is 32 bytes");

    f
}

/// Reads an FsRepr from [u8] of length 32
/// This will panic (abort) if length provided is
/// not correct
fn read_fs(from: &[u8]) -> FsRepr {
    assert_eq!(from.len(), 32);

    let mut f = <<Bls12 as JubjubEngine>::Fs as PrimeField>::Repr::default();
    f.read_le(from).expect("length is 32 bytes");

    f
}

/// Reads an FsRepr from [u8] of length 32
/// and multiplies it by the given base.
/// This will panic (abort) if length provided is
/// not correct
fn fixed_scalar_mult(from: &[u8], p_g: FixedGenerators) -> edwards::Point<Bls12, PrimeOrder> {
    let f = read_fs(from);

    JUBJUB.generator(p_g).mul(f, &JUBJUB)
}

#[no_mangle]
pub extern "system" fn librustzcash_init_zksnark_params(
    spend_path: *const c_char,
    spend_hash: *const c_char,
    output_path: *const c_char,
    output_hash: *const c_char,
    sprout_path: *const c_char,
    sprout_hash: *const c_char,
) {
    // Initialize jubjub parameters here
    lazy_static::initialize(&JUBJUB);

    let spend_hash = unsafe { CStr::from_ptr(spend_hash) }
        .to_str()
        .expect("hash should be a valid string");

    let output_hash = unsafe { CStr::from_ptr(output_hash) }
        .to_str()
        .expect("hash should be a valid string");

    let sprout_hash = unsafe { CStr::from_ptr(sprout_hash) }
        .to_str()
        .expect("hash should be a valid string");

    // These should be valid CStr's, but the decoding may fail on Windows
    // so we may need to use OSStr or something.
    let spend_path = unsafe { CStr::from_ptr(spend_path) }
        .to_str()
        .expect("parameter path encoding error");
    let output_path = unsafe { CStr::from_ptr(output_path) }
        .to_str()
        .expect("parameter path encoding error");
    let sprout_path = unsafe { CStr::from_ptr(sprout_path) }
        .to_str()
        .expect("parameter path encoding error");

    // Load params
    let (spend_params, spend_vk, output_params, output_vk, sprout_vk) = load_parameters(
        spend_path,
        spend_hash,
        output_path,
        output_hash,
        sprout_path,
        sprout_hash,
    );

    // Caller is responsible for calling this function once, so
    // these global mutations are safe.
    unsafe {
        SAPLING_SPEND_PARAMS = Some(spend_params);
        SAPLING_OUTPUT_PARAMS = Some(output_params);
        SPROUT_GROTH16_PARAMS_PATH = Some(sprout_path.to_owned());

        SAPLING_SPEND_VK = Some(spend_vk);
        SAPLING_OUTPUT_VK = Some(output_vk);
        SPROUT_GROTH16_VK = Some(sprout_vk);
    }
}

#[no_mangle]
pub extern "system" fn librustzcash_tree_uncommitted(result: *mut [c_uchar; 32]) {
    let tmp = sapling_crypto::primitives::Note::<Bls12>::uncommitted().into_repr();

    // Should be okay, caller is responsible for ensuring the pointer
    // is a valid pointer to 32 bytes that can be mutated.
    let result = unsafe { &mut *result };

    write_le(tmp, &mut result[..]);
}

#[no_mangle]
pub extern "system" fn librustzcash_merkle_hash(
    depth: size_t,
    a: *const [c_uchar; 32],
    b: *const [c_uchar; 32],
    result: *mut [c_uchar; 32],
) {
    // Should be okay, because caller is responsible for ensuring
    // the pointer is a valid pointer to 32 bytes, and that is the
    // size of the representation
    let a_repr = read_le(unsafe { &(&*a)[..] });

    // Should be okay, because caller is responsible for ensuring
    // the pointer is a valid pointer to 32 bytes, and that is the
    // size of the representation
    let b_repr = read_le(unsafe { &(&*b)[..] });

    let mut lhs = [false; 256];
    let mut rhs = [false; 256];

    for (a, b) in lhs.iter_mut().rev().zip(BitIterator::new(a_repr)) {
        *a = b;
    }

    for (a, b) in rhs.iter_mut().rev().zip(BitIterator::new(b_repr)) {
        *a = b;
    }

    let tmp = pedersen_hash::<Bls12, _>(
        Personalization::MerkleTree(depth),
        lhs.iter()
            .map(|&x| x)
            .take(Fr::NUM_BITS as usize)
            .chain(rhs.iter().map(|&x| x).take(Fr::NUM_BITS as usize)),
        &JUBJUB,
    ).into_xy()
        .0
        .into_repr();

    // Should be okay, caller is responsible for ensuring the pointer
    // is a valid pointer to 32 bytes that can be mutated.
    let result = unsafe { &mut *result };

    write_le(tmp, &mut result[..]);
}

#[no_mangle] // ToScalar
pub extern "system" fn librustzcash_to_scalar(
    input: *const [c_uchar; 64],
    result: *mut [c_uchar; 32],
) {
    // Should be okay, because caller is responsible for ensuring
    // the pointer is a valid pointer to 32 bytes, and that is the
    // size of the representation
    let scalar = <Bls12 as JubjubEngine>::Fs::to_uniform(unsafe { &(&*input)[..] }).into_repr();

    let result = unsafe { &mut *result };

    scalar
        .write_le(&mut result[..])
        .expect("length is 32 bytes");
}

#[no_mangle]
pub extern "system" fn librustzcash_ask_to_ak(
    ask: *const [c_uchar; 32],
    result: *mut [c_uchar; 32],
) {
    let ask = unsafe { &*ask };
    let ak = fixed_scalar_mult(ask, FixedGenerators::SpendingKeyGenerator);

    let result = unsafe { &mut *result };

    ak.write(&mut result[..]).expect("length is 32 bytes");
}

#[no_mangle]
pub extern "system" fn librustzcash_nsk_to_nk(
    nsk: *const [c_uchar; 32],
    result: *mut [c_uchar; 32],
) {
    let nsk = unsafe { &*nsk };
    let nk = fixed_scalar_mult(nsk, FixedGenerators::ProofGenerationKey);

    let result = unsafe { &mut *result };

    nk.write(&mut result[..]).expect("length is 32 bytes");
}

#[no_mangle]
pub extern "system" fn librustzcash_crh_ivk(
    ak: *const [c_uchar; 32],
    nk: *const [c_uchar; 32],
    result: *mut [c_uchar; 32],
) {
    let ak = unsafe { &*ak };
    let nk = unsafe { &*nk };

    let mut h = Blake2s::with_params(32, &[], &[], CRH_IVK_PERSONALIZATION);
    h.update(ak);
    h.update(nk);
    let mut h = h.finalize().as_ref().to_vec();

    // Drop the last five bits, so it can be interpreted as a scalar.
    h[31] &= 0b0000_0111;

    let result = unsafe { &mut *result };

    result.copy_from_slice(&h);
}

#[no_mangle]
pub extern "system" fn librustzcash_check_diversifier(diversifier: *const [c_uchar; 11]) -> bool {
    let diversifier = sapling_crypto::primitives::Diversifier(unsafe { *diversifier });
    diversifier.g_d::<Bls12>(&JUBJUB).is_some()
}

#[no_mangle]
pub extern "system" fn librustzcash_ivk_to_pkd(
    ivk: *const [c_uchar; 32],
    diversifier: *const [c_uchar; 11],
    result: *mut [c_uchar; 32],
) -> bool {
    let ivk = read_fs(unsafe { &*ivk });
    let diversifier = sapling_crypto::primitives::Diversifier(unsafe { *diversifier });
    if let Some(g_d) = diversifier.g_d::<Bls12>(&JUBJUB) {
        let pk_d = g_d.mul(ivk, &JUBJUB);

        let result = unsafe { &mut *result };

        pk_d.write(&mut result[..]).expect("length is 32 bytes");

        true
    } else {
        false
    }
}

/// Test generation of commitment randomness
#[test]
fn test_gen_r() {
    let mut r1 = [0u8; 32];
    let mut r2 = [0u8; 32];

    // Verify different r values are generated
    librustzcash_sapling_generate_r(&mut r1);
    librustzcash_sapling_generate_r(&mut r2);
    assert_ne!(r1, r2);

    // Verify r values are valid in the field
    let mut repr = FsRepr::default();
    repr.read_le(&r1[..]).expect("length is not 32 bytes");
    let _ = Fs::from_repr(repr).unwrap();
    repr.read_le(&r2[..]).expect("length is not 32 bytes");
    let _ = Fs::from_repr(repr).unwrap();
}

/// Return 32 byte random scalar, uniformly.
#[no_mangle]
pub extern "system" fn librustzcash_sapling_generate_r(result: *mut [c_uchar; 32]) {
    // create random 64 byte buffer
    let mut rng = OsRng::new().expect("should be able to construct RNG");
    let mut buffer = [0u8; 64];
    for i in 0..buffer.len() {
        buffer[i] = rng.gen();
    }

    // reduce to uniform value
    let r = <Bls12 as JubjubEngine>::Fs::to_uniform(&buffer[..]);
    let result = unsafe { &mut *result };
    r.into_repr()
        .write_le(&mut result[..])
        .expect("result must be 32 bytes");
}

// Private utility function to get Note from C parameters
fn priv_get_note(
    diversifier: *const [c_uchar; 11],
    pk_d: *const [c_uchar; 32],
    value: uint64_t,
    r: *const [c_uchar; 32],
) -> Result<sapling_crypto::primitives::Note<Bls12>, ()> {
    let diversifier = sapling_crypto::primitives::Diversifier(unsafe { *diversifier });
    let g_d = match diversifier.g_d::<Bls12>(&JUBJUB) {
        Some(g_d) => g_d,
        None => return Err(()),
    };

    let pk_d = match edwards::Point::<Bls12, Unknown>::read(&(unsafe { &*pk_d })[..], &JUBJUB) {
        Ok(p) => p,
        Err(_) => return Err(()),
    };

    let pk_d = match pk_d.as_prime_order(&JUBJUB) {
        Some(pk_d) => pk_d,
        None => return Err(()),
    };

    // Deserialize randomness
    let r = match Fs::from_repr(read_fs(&(unsafe { &*r })[..])) {
        Ok(r) => r,
        Err(_) => return Err(()),
    };

    let note = sapling_crypto::primitives::Note {
        value,
        g_d,
        pk_d,
        r,
    };

    Ok(note)
}

/// Compute Sapling note nullifier.
#[no_mangle]
pub extern "system" fn librustzcash_sapling_compute_nf(
    diversifier: *const [c_uchar; 11],
    pk_d: *const [c_uchar; 32],
    value: uint64_t,
    r: *const [c_uchar; 32],
    ak: *const [c_uchar; 32],
    nk: *const [c_uchar; 32],
    position: uint64_t,
    result: *mut [c_uchar; 32],
) -> bool {
    let note = match priv_get_note(diversifier, pk_d, value, r) {
        Ok(p) => p,
        Err(_) => return false,
    };

    let ak = match edwards::Point::<Bls12, Unknown>::read(&(unsafe { &*ak })[..], &JUBJUB) {
        Ok(p) => p,
        Err(_) => return false,
    };

    let ak = match ak.as_prime_order(&JUBJUB) {
        Some(ak) => ak,
        None => return false,
    };

    let nk = match edwards::Point::<Bls12, Unknown>::read(&(unsafe { &*nk })[..], &JUBJUB) {
        Ok(p) => p,
        Err(_) => return false,
    };

    let nk = match nk.as_prime_order(&JUBJUB) {
        Some(nk) => nk,
        None => return false,
    };

    let vk = ViewingKey { ak, nk };
    let nf = note.nf(&vk, position, &JUBJUB);
    let result = unsafe { &mut *result };
    result.copy_from_slice(&nf);

    true
}

/// Compute Sapling note commitment.
#[no_mangle]
pub extern "system" fn librustzcash_sapling_compute_cm(
    diversifier: *const [c_uchar; 11],
    pk_d: *const [c_uchar; 32],
    value: uint64_t,
    r: *const [c_uchar; 32],
    result: *mut [c_uchar; 32],
) -> bool {
    let note = match priv_get_note(diversifier, pk_d, value, r) {
        Ok(p) => p,
        Err(_) => return false,
    };

    let result = unsafe { &mut *result };
    write_le(note.cm(&JUBJUB).into_repr(), &mut result[..]);

    true
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_ka_agree(
    p: *const [c_uchar; 32],
    sk: *const [c_uchar; 32],
    result: *mut [c_uchar; 32],
) -> bool {
    // Deserialize p
    let p = match edwards::Point::<Bls12, Unknown>::read(&(unsafe { &*p })[..], &JUBJUB) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // Deserialize sk
    let sk = match Fs::from_repr(read_fs(&(unsafe { &*sk })[..])) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // Multiply by 8
    let p = p.mul_by_cofactor(&JUBJUB);

    // Multiply by sk
    let p = p.mul(sk, &JUBJUB);

    // Produce result
    let result = unsafe { &mut *result };
    p.write(&mut result[..]).expect("length is not 32 bytes");

    true
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_ka_derivepublic(
    diversifier: *const [c_uchar; 11],
    esk: *const [c_uchar; 32],
    result: *mut [c_uchar; 32],
) -> bool {
    let diversifier = sapling_crypto::primitives::Diversifier(unsafe { *diversifier });

    // Compute g_d from the diversifier
    let g_d = match diversifier.g_d::<Bls12>(&JUBJUB) {
        Some(g) => g,
        None => return false,
    };

    // Deserialize esk
    let esk = match Fs::from_repr(read_fs(&(unsafe { &*esk })[..])) {
        Ok(p) => p,
        Err(_) => return false,
    };

    let p = g_d.mul(esk, &JUBJUB);

    let result = unsafe { &mut *result };
    p.write(&mut result[..]).expect("length is not 32 bytes");

    true
}

#[no_mangle]
pub extern "system" fn librustzcash_eh_isvalid(
    n: uint32_t,
    k: uint32_t,
    input: *const c_uchar,
    input_len: size_t,
    nonce: *const c_uchar,
    nonce_len: size_t,
    soln: *const c_uchar,
    soln_len: size_t,
) -> bool {
    if (k >= n) || (n % 8 != 0) || (soln_len != (1 << k) * ((n / (k + 1)) as usize + 1) / 8) {
        return false;
    }
    let rs_input = unsafe { slice::from_raw_parts(input, input_len) };
    let rs_nonce = unsafe { slice::from_raw_parts(nonce, nonce_len) };
    let rs_soln = unsafe { slice::from_raw_parts(soln, soln_len) };
    equihash::is_valid_solution(n, k, rs_input, rs_nonce, rs_soln)
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_verification_ctx_init(
) -> *mut SaplingVerificationContext {
    let ctx = Box::new(SaplingVerificationContext::new());

    Box::into_raw(ctx)
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_verification_ctx_free(
    ctx: *mut SaplingVerificationContext,
) {
    drop(unsafe { Box::from_raw(ctx) });
}

const GROTH_PROOF_SIZE: usize = 48 // π_A
    + 96 // π_B
    + 48; // π_C

#[no_mangle]
pub extern "system" fn librustzcash_sapling_check_spend(
    ctx: *mut SaplingVerificationContext,
    cv: *const [c_uchar; 32],
    anchor: *const [c_uchar; 32],
    nullifier: *const [c_uchar; 32],
    rk: *const [c_uchar; 32],
    zkproof: *const [c_uchar; GROTH_PROOF_SIZE],
    spend_auth_sig: *const [c_uchar; 64],
    sighash_value: *const [c_uchar; 32],
) -> bool {
    // Deserialize the value commitment
    let cv = match edwards::Point::<Bls12, Unknown>::read(&(unsafe { &*cv })[..], &JUBJUB) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // Deserialize the anchor, which should be an element
    // of Fr.
    let anchor = match Fr::from_repr(read_le(&(unsafe { &*anchor })[..])) {
        Ok(a) => a,
        Err(_) => return false,
    };

    // Deserialize rk
    let rk = match redjubjub::PublicKey::<Bls12>::read(&(unsafe { &*rk })[..], &JUBJUB) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // Deserialize the signature
    let spend_auth_sig = match Signature::read(&(unsafe { &*spend_auth_sig })[..]) {
        Ok(sig) => sig,
        Err(_) => return false,
    };

    // Deserialize the proof
    let zkproof = match Proof::<Bls12>::read(&(unsafe { &*zkproof })[..]) {
        Ok(p) => p,
        Err(_) => return false,
    };

    unsafe { &mut *ctx }.check_spend(
        cv,
        anchor,
        unsafe { &*nullifier },
        rk,
        unsafe { &*sighash_value },
        spend_auth_sig,
        zkproof,
        unsafe { SAPLING_SPEND_VK.as_ref() }.unwrap(),
        &JUBJUB,
    )
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_check_output(
    ctx: *mut SaplingVerificationContext,
    cv: *const [c_uchar; 32],
    cm: *const [c_uchar; 32],
    epk: *const [c_uchar; 32],
    zkproof: *const [c_uchar; GROTH_PROOF_SIZE],
) -> bool {
    // Deserialize the value commitment
    let cv = match edwards::Point::<Bls12, Unknown>::read(&(unsafe { &*cv })[..], &JUBJUB) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // Deserialize the commitment, which should be an element
    // of Fr.
    let cm = match Fr::from_repr(read_le(&(unsafe { &*cm })[..])) {
        Ok(a) => a,
        Err(_) => return false,
    };

    // Deserialize the ephemeral key
    let epk = match edwards::Point::<Bls12, Unknown>::read(&(unsafe { &*epk })[..], &JUBJUB) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // Deserialize the proof
    let zkproof = match Proof::<Bls12>::read(&(unsafe { &*zkproof })[..]) {
        Ok(p) => p,
        Err(_) => return false,
    };

    unsafe { &mut *ctx }.check_output(
        cv,
        cm,
        epk,
        zkproof,
        unsafe { SAPLING_OUTPUT_VK.as_ref() }.unwrap(),
        &JUBJUB,
    )
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_final_check(
    ctx: *mut SaplingVerificationContext,
    value_balance: int64_t,
    binding_sig: *const [c_uchar; 64],
    sighash_value: *const [c_uchar; 32],
) -> bool {
    // Deserialize the signature
    let binding_sig = match Signature::read(&(unsafe { &*binding_sig })[..]) {
        Ok(sig) => sig,
        Err(_) => return false,
    };

    unsafe { &*ctx }.final_check(
        value_balance,
        unsafe { &*sighash_value },
        binding_sig,
        &JUBJUB,
    )
}

#[no_mangle]
pub extern "system" fn librustzcash_sprout_prove(
    proof_out: *mut [c_uchar; GROTH_PROOF_SIZE],

    phi: *const [c_uchar; 32],
    rt: *const [c_uchar; 32],
    h_sig: *const [c_uchar; 32],

    // First input
    in_sk1: *const [c_uchar; 32],
    in_value1: uint64_t,
    in_rho1: *const [c_uchar; 32],
    in_r1: *const [c_uchar; 32],
    in_auth1: *const [c_uchar; 1 + 33 * SPROUT_TREE_DEPTH + 8],

    // Second input
    in_sk2: *const [c_uchar; 32],
    in_value2: uint64_t,
    in_rho2: *const [c_uchar; 32],
    in_r2: *const [c_uchar; 32],
    in_auth2: *const [c_uchar; 1 + 33 * SPROUT_TREE_DEPTH + 8],

    // First output
    out_pk1: *const [c_uchar; 32],
    out_value1: uint64_t,
    out_r1: *const [c_uchar; 32],

    // Second output
    out_pk2: *const [c_uchar; 32],
    out_value2: uint64_t,
    out_r2: *const [c_uchar; 32],

    // Public value
    vpub_old: uint64_t,
    vpub_new: uint64_t,
) {
    let phi = unsafe { *phi };
    let rt = unsafe { *rt };
    let h_sig = unsafe { *h_sig };
    let in_sk1 = unsafe { *in_sk1 };
    let in_rho1 = unsafe { *in_rho1 };
    let in_r1 = unsafe { *in_r1 };
    let in_auth1 = unsafe { *in_auth1 };
    let in_sk2 = unsafe { *in_sk2 };
    let in_rho2 = unsafe { *in_rho2 };
    let in_r2 = unsafe { *in_r2 };
    let in_auth2 = unsafe { *in_auth2 };
    let out_pk1 = unsafe { *out_pk1 };
    let out_r1 = unsafe { *out_r1 };
    let out_pk2 = unsafe { *out_pk2 };
    let out_r2 = unsafe { *out_r2 };

    let mut inputs = Vec::with_capacity(2);
    {
        let mut handle_input = |sk, value, rho, r, mut auth: &[u8]| {
            let value = Some(value);
            let rho = Some(sprout::UniqueRandomness(rho));
            let r = Some(sprout::CommitmentRandomness(r));
            let a_sk = Some(sprout::SpendingKey(sk));

            // skip the first byte
            assert_eq!(auth[0], SPROUT_TREE_DEPTH as u8);
            auth = &auth[1..];

            let mut auth_path = [None; SPROUT_TREE_DEPTH];
            for i in (0..SPROUT_TREE_DEPTH).rev() {
                // skip length of inner vector
                assert_eq!(auth[0], 32);
                auth = &auth[1..];

                let mut sibling = [0u8; 32];
                sibling.copy_from_slice(&auth[0..32]);
                auth = &auth[32..];

                auth_path[i] = Some((sibling, false));
            }

            let mut position = auth
                .read_u64::<LittleEndian>()
                .expect("should have had index at the end");

            for i in 0..SPROUT_TREE_DEPTH {
                auth_path[i].as_mut().map(|p| p.1 = (position & 1) == 1);

                position >>= 1;
            }

            inputs.push(sprout::JSInput {
                value: value,
                a_sk: a_sk,
                rho: rho,
                r: r,
                auth_path: auth_path,
            });
        };

        handle_input(in_sk1, in_value1, in_rho1, in_r1, &in_auth1[..]);
        handle_input(in_sk2, in_value2, in_rho2, in_r2, &in_auth2[..]);
    }

    let mut outputs = Vec::with_capacity(2);
    {
        let mut handle_output = |a_pk, value, r| {
            outputs.push(sprout::JSOutput {
                value: Some(value),
                a_pk: Some(sprout::PayingKey(a_pk)),
                r: Some(sprout::CommitmentRandomness(r)),
            });
        };

        handle_output(out_pk1, out_value1, out_r1);
        handle_output(out_pk2, out_value2, out_r2);
    }

    let js = sprout::JoinSplit {
        vpub_old: Some(vpub_old),
        vpub_new: Some(vpub_new),
        h_sig: Some(h_sig),
        phi: Some(phi),
        inputs: inputs,
        outputs: outputs,
        rt: Some(rt),
    };

    // Load parameters from disk
    let sprout_fs = File::open(
        unsafe { &SPROUT_GROTH16_PARAMS_PATH }
            .as_ref()
            .expect("parameters should have been initialized"),
    ).expect("couldn't load Sprout groth16 parameters file");

    let mut sprout_fs = BufReader::with_capacity(1024 * 1024, sprout_fs);

    let params = Parameters::<Bls12>::read(&mut sprout_fs, false)
        .expect("couldn't deserialize Sprout JoinSplit parameters file");

    drop(sprout_fs);

    // Initialize secure RNG
    let mut rng = OsRng::new().expect("should be able to construct RNG");

    let proof = create_random_proof(js, &params, &mut rng).expect("proving should not fail");

    proof
        .write(&mut (unsafe { &mut *proof_out })[..])
        .expect("should be able to serialize a proof");
}

#[no_mangle]
pub extern "system" fn librustzcash_sprout_verify(
    proof: *const [c_uchar; GROTH_PROOF_SIZE],
    rt: *const [c_uchar; 32],
    h_sig: *const [c_uchar; 32],
    mac1: *const [c_uchar; 32],
    mac2: *const [c_uchar; 32],
    nf1: *const [c_uchar; 32],
    nf2: *const [c_uchar; 32],
    cm1: *const [c_uchar; 32],
    cm2: *const [c_uchar; 32],
    vpub_old: uint64_t,
    vpub_new: uint64_t,
) -> bool {
    // Prepare the public input for the verifier
    let mut public_input = Vec::with_capacity((32 * 8) + (8 * 2));
    public_input.extend(unsafe { &(&*rt)[..] });
    public_input.extend(unsafe { &(&*h_sig)[..] });
    public_input.extend(unsafe { &(&*nf1)[..] });
    public_input.extend(unsafe { &(&*mac1)[..] });
    public_input.extend(unsafe { &(&*nf2)[..] });
    public_input.extend(unsafe { &(&*mac2)[..] });
    public_input.extend(unsafe { &(&*cm1)[..] });
    public_input.extend(unsafe { &(&*cm2)[..] });
    public_input.write_u64::<LittleEndian>(vpub_old).unwrap();
    public_input.write_u64::<LittleEndian>(vpub_new).unwrap();

    let public_input = multipack::bytes_to_bits(&public_input);
    let public_input = multipack::compute_multipacking::<Bls12>(&public_input);

    let proof = match Proof::read(unsafe { &(&*proof)[..] }) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // Verify the proof
    match verify_proof(
        unsafe { SPROUT_GROTH16_VK.as_ref() }.expect("parameters should have been initialized"),
        &proof,
        &public_input[..],
    ) {
        // No error, and proof verification successful
        Ok(true) => true,

        // Any other case
        _ => false,
    }
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_output_proof(
    ctx: *mut SaplingProvingContext,
    esk: *const [c_uchar; 32],
    diversifier: *const [c_uchar; 11],
    pk_d: *const [c_uchar; 32],
    rcm: *const [c_uchar; 32],
    value: uint64_t,
    cv: *mut [c_uchar; 32],
    zkproof: *mut [c_uchar; GROTH_PROOF_SIZE],
) -> bool {
    // Grab `esk`, which the caller should have constructed for the DH key exchange.
    let esk = match Fs::from_repr(read_fs(&(unsafe { &*esk })[..])) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // Grab the diversifier from the caller.
    let diversifier = sapling_crypto::primitives::Diversifier(unsafe { *diversifier });

    // Grab pk_d from the caller.
    let pk_d = match edwards::Point::<Bls12, Unknown>::read(&(unsafe { &*pk_d })[..], &JUBJUB) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // pk_d should be prime order.
    let pk_d = match pk_d.as_prime_order(&JUBJUB) {
        Some(p) => p,
        None => return false,
    };

    // Construct a payment address
    let payment_address = sapling_crypto::primitives::PaymentAddress {
        pk_d: pk_d,
        diversifier: diversifier,
    };

    // The caller provides the commitment randomness for the output note
    let rcm = match Fs::from_repr(read_fs(&(unsafe { &*rcm })[..])) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // Create proof
    let (proof, value_commitment) = unsafe { &mut *ctx }.output_proof(
        esk,
        payment_address,
        rcm,
        value,
        unsafe { SAPLING_OUTPUT_PARAMS.as_ref() }.unwrap(),
        &JUBJUB,
    );

    // Write the proof out to the caller
    proof
        .write(&mut (unsafe { &mut *zkproof })[..])
        .expect("should be able to serialize a proof");

    // Write the value commitment to the caller
    value_commitment
        .write(&mut (unsafe { &mut *cv })[..])
        .expect("should be able to serialize rcv");

    true
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_spend_sig(
    ask: *const [c_uchar; 32],
    ar: *const [c_uchar; 32],
    sighash: *const [c_uchar; 32],
    result: *mut [c_uchar; 64],
) -> bool {
    // The caller provides the re-randomization of `ak`.
    let ar = match Fs::from_repr(read_fs(&(unsafe { &*ar })[..])) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // The caller provides `ask`, the spend authorizing key.
    let ask = match redjubjub::PrivateKey::<Bls12>::read(&(unsafe { &*ask })[..]) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // Do the signing
    let sig = spend_sig(ask, ar, unsafe { &*sighash }, &JUBJUB);

    // Write out the signature
    sig.write(&mut (unsafe { &mut *result })[..])
        .expect("result should be 64 bytes");

    true
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_binding_sig(
    ctx: *const SaplingProvingContext,
    value_balance: int64_t,
    sighash: *const [c_uchar; 32],
    result: *mut [c_uchar; 64],
) -> bool {
    // Sign
    let sig = match unsafe { &*ctx }.binding_sig(value_balance, unsafe { &*sighash }, &JUBJUB) {
        Ok(s) => s,
        Err(_) => return false,
    };

    // Write out signature
    sig.write(&mut (unsafe { &mut *result })[..])
        .expect("result should be 64 bytes");

    true
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_spend_proof(
    ctx: *mut SaplingProvingContext,
    ak: *const [c_uchar; 32],
    nsk: *const [c_uchar; 32],
    diversifier: *const [c_uchar; 11],
    rcm: *const [c_uchar; 32],
    ar: *const [c_uchar; 32],
    value: uint64_t,
    anchor: *const [c_uchar; 32],
    witness: *const [c_uchar; 1 + 33 * SAPLING_TREE_DEPTH + 8],
    cv: *mut [c_uchar; 32],
    rk_out: *mut [c_uchar; 32],
    zkproof: *mut [c_uchar; GROTH_PROOF_SIZE],
) -> bool {
    // Grab `ak` from the caller, which should be a point.
    let ak = match edwards::Point::<Bls12, Unknown>::read(&(unsafe { &*ak })[..], &JUBJUB) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // `ak` should be prime order.
    let ak = match ak.as_prime_order(&JUBJUB) {
        Some(p) => p,
        None => return false,
    };

    // Grab `nsk` from the caller
    let nsk = match Fs::from_repr(read_fs(&(unsafe { &*nsk })[..])) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // Construct the proof generation key
    let proof_generation_key = ProofGenerationKey {
        ak: ak.clone(),
        nsk,
    };

    // Grab the diversifier from the caller
    let diversifier = sapling_crypto::primitives::Diversifier(unsafe { *diversifier });

    // The caller chooses the note randomness
    let rcm = match Fs::from_repr(read_fs(&(unsafe { &*rcm })[..])) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // The caller also chooses the re-randomization of ak
    let ar = match Fs::from_repr(read_fs(&(unsafe { &*ar })[..])) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // We need to compute the anchor of the Spend.
    let anchor = match Fr::from_repr(read_le(unsafe { &(&*anchor)[..] })) {
        Ok(p) => p,
        Err(_) => return false,
    };

    // The witness contains the incremental tree witness information, in a
    // weird serialized format.
    let witness = match CommitmentTreeWitness::from_slice(unsafe { &(&*witness)[..] }) {
        Ok(w) => w,
        Err(_) => return false,
    };

    // Create proof
    let (proof, value_commitment, rk) = unsafe { &mut *ctx }
        .spend_proof(
            proof_generation_key,
            diversifier,
            rcm,
            ar,
            value,
            anchor,
            witness,
            unsafe { SAPLING_SPEND_PARAMS.as_ref() }.unwrap(),
            unsafe { SAPLING_SPEND_VK.as_ref() }.unwrap(),
            &JUBJUB,
        )
        .expect("proving should not fail");

    // Write value commitment to caller
    value_commitment
        .write(&mut unsafe { &mut *cv }[..])
        .expect("should be able to serialize cv");

    // Write proof out to caller
    proof
        .write(&mut (unsafe { &mut *zkproof })[..])
        .expect("should be able to serialize a proof");

    // Write out `rk` to the caller
    rk.write(&mut unsafe { &mut *rk_out }[..])
        .expect("should be able to write to rk_out");

    true
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_proving_ctx_init() -> *mut SaplingProvingContext {
    let ctx = Box::new(SaplingProvingContext::new());

    Box::into_raw(ctx)
}

#[no_mangle]
pub extern "system" fn librustzcash_sapling_proving_ctx_free(ctx: *mut SaplingProvingContext) {
    drop(unsafe { Box::from_raw(ctx) });
}
