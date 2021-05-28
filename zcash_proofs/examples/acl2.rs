use bellman::{Circuit, ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};
use bls12_381::Scalar;
use std::env;
use std::fmt;
use zcash_proofs::circuit::{
    sapling::{Output, Spend},
    sprout::{JSInput, JSOutput, JoinSplit},
};

use std::rc::Rc;
use std::cell::RefCell;

fn compute_path(ns: &[String], this: String) -> String {
    if this.chars().any(|a| a == '/') {
        panic!("'/' is not allowed in names");
    }

    let mut name = String::new();

    let mut needs_separation = false;
    for ns in ns.iter().chain(Some(&this).into_iter()) {
        if needs_separation {
            name += "/";
        }

        name += ns;
        needs_separation = true;
    }

    name
}

/// Converts a bellman path to an ACL2 variable name.
fn acl2ize(s: &str) -> String {
    s.replace(' ', "_")
    // The following was the original code,
    // but it maps both space and slash to underscore.
    // We use instead the code above, which preserves slashes,
    // which are legal in ACL2 symbols.
    // s.replace(' ', "_").replace('/', "_")
}

struct Acl2Cs {
    current_namespace: Vec<String>,
    inputs: Vec<String>,
    aux: Vec<String>,
    constraints: Vec<(
        LinearCombination<Scalar>,
        LinearCombination<Scalar>,
        LinearCombination<Scalar>,
    )>,
}

impl Acl2Cs {
    fn new() -> Self {
        Acl2Cs {
            current_namespace: vec![],
            inputs: vec!["1".into()],
            aux: vec![],
            constraints: vec![],
        }
    }
}

impl fmt::Display for Acl2Cs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;

        // Hard-code the BLS12-381 scalar modulus.
        // In acl2 hex integers start with `#x`.
        writeln!(
            f,
            "(R1CS::PRIME . #x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)"
        )?;

        // Circuit variables
        write!(f, "(R1CS::VARS")?;
        // ACL2 format doesn't include the constant 1.
        for var in self.inputs.iter().skip(1) {
            write!(f, " {}", var)?;
        }
        for var in &self.aux {
            write!(f, " {}", var)?;
        }
        writeln!(f, ")")?;

        // Constraints.
        let write_lc = |f: &mut fmt::Formatter<'_>, name, lc: &LinearCombination<Scalar>| {
            write!(f, "({}", name)?;
            for (var, coeff) in lc.as_ref() {
                write!(
                    f,
                    " ({} {})",
                    coeff.to_string().replace("0x", "#x"),
                    match var.get_unchecked() {
                        Index::Input(i) => &self.inputs[i],
                        Index::Aux(i) => &self.aux[i],
                    }
                )?;
            }
            write!(f, ")")?;
            Ok(())
        };
        write!(f, "(R1CS::CONSTRAINTS ")?;
        for (a, b, c) in &self.constraints {
            write!(f, "(")?;
            write_lc(f, "R1CS::A", a)?;
            write_lc(f, "R1CS::B", b)?;
            write_lc(f, "R1CS::C", c)?;
            writeln!(f, ")")?;
        }
        write!(f, ")")?;

        writeln!(f, ")")
    }
}

impl ConstraintSystem<Scalar> for Acl2Cs {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, annotation: A, _: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.aux.len();
        let path = compute_path(&self.current_namespace, annotation().into());
        self.aux.push(acl2ize(&path));
        Ok(Variable::new_unchecked(Index::Aux(index)))
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, _: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.inputs.len();
        let path = compute_path(&self.current_namespace, annotation().into());
        self.inputs.push(acl2ize(&path));
        Ok(Variable::new_unchecked(Index::Input(index)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LB: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LC: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
    {
        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        self.constraints.push((a, b, c));
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        let name = name_fn().into();
        self.current_namespace.push(name);
    }

    fn pop_namespace(&mut self) {
        assert!(self.current_namespace.pop().is_some());
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

/// A tree of constraints.
struct Tree {
    parent: Option<Rc<RefCell<Tree>>>,
    name: String,
    children: Vec<Rc<RefCell<Tree>>>,
    constraints: Vec<(LinearCombination<Scalar>,
                      LinearCombination<Scalar>,
                      LinearCombination<Scalar>)>
}

impl Tree {

    fn new_root() -> Self {
        Tree {
            parent: None,
            name: String::from(""),
            children: vec![],
            constraints: vec![]
        }
    }

    fn new_child(parent: Rc<RefCell<Tree>>, name: String) -> Self {
        Tree {
            parent: Some(parent),
            name: name,
            children: vec![],
            constraints: vec![]
        }
    }

}

/// A tree-structured constraint system.
struct TreeCs {
    current_namespace: Vec<String>,
    inputs: Vec<String>,
    aux: Vec<String>,
    tree: Rc<RefCell<Tree>>,
    current: Rc<RefCell<Tree>>
}

impl TreeCs {

    fn new() -> Self {
        let tree = Rc::new(RefCell::new(Tree::new_root()));
        let current = tree.clone();
        TreeCs {
            current_namespace: vec![],
            inputs: vec!["1".into()],
            aux: vec![],
            tree: tree,
            current: current
        }
    }

}

impl Tree {

    fn fmt(&self,
           f: &mut fmt::Formatter<'_>,
           inputs: &Vec<String>,
           aux: &Vec<String>)
           -> fmt::Result {
        let write_lc =
            |f: &mut fmt::Formatter<'_>, name, lc: &LinearCombination<Scalar>| {
                write!(f, "({}", name)?;
                for (var, coeff) in lc.as_ref() {
                    write!(
                        f,
                        " ({} {})",
                        coeff.to_string().replace("0x", "#x"),
                        match var.get_unchecked() {
                            Index::Input(i) => &inputs[i],
                            Index::Aux(i) => &aux[i],
                        }
                    )?;
                }
                write!(f, ")")?;
                Ok(())
            };

        write!(f, "(\"{}\"", self.name)?;

        write!(f, " (R1CS::CONSTRAINTS ")?;
        for (a, b, c) in &self.constraints {
            write!(f, "(")?;
            write_lc(f, "R1CS::A", a)?;
            write_lc(f, "R1CS::B", b)?;
            write_lc(f, "R1CS::C", c)?;
            writeln!(f, ")")?;
        }
        write!(f, ")")?;
        for child in &self.children {
            write!(f, " ")?;
            (*child).borrow().fmt(f, inputs, aux)?;
        }
        write!(f, ") ")?;
        Ok(())
    }

}

impl fmt::Display for TreeCs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;

        // Hard-code the BLS12-381 scalar modulus.
        // In acl2 hex integers start with `#x`.
        writeln!(
            f,
            "(R1CS::PRIME . #x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)"
        )?;

        // Circuit variables
        write!(f, "(R1CS::VARS")?;
        // ACL2 format doesn't include the constant 1.
        for var in self.inputs.iter().skip(1) {
            write!(f, " {}", var)?;
        }
        for var in &self.aux {
            write!(f, " {}", var)?;
        }
        writeln!(f, ")")?;

        // Constraints.
        (*self.tree).borrow().fmt(f, &self.inputs, &self.aux)?;

        writeln!(f, ")")
    }
}

impl ConstraintSystem<Scalar> for TreeCs {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, annotation: A, _: F)
                       -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.aux.len();
        let path = compute_path(&self.current_namespace, annotation().into());
        self.aux.push(acl2ize(&path));
        Ok(Variable::new_unchecked(Index::Aux(index)))
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, _: F)
                             -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.inputs.len();
        let path = compute_path(&self.current_namespace, annotation().into());
        self.inputs.push(acl2ize(&path));
        Ok(Variable::new_unchecked(Index::Input(index)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LB: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LC: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
    {
        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());
        (*self.current).borrow_mut().constraints.push((a, b, c));
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        let name = name_fn().into();
        let name_clone = name.clone();
        self.current_namespace.push(name);
        let tree =
            Rc::new
            (RefCell::new
             (Tree::new_child(self.current.clone(), name_clone)));
        (*self.current).borrow_mut().children.push(tree.clone());
        self.current = tree;
    }

    fn pop_namespace(&mut self) {
        assert!(self.current_namespace.pop().is_some());
        let parent = (*self.current).borrow().parent.clone();
        match parent {
            Some(parent) => {
                self.current = parent.clone();
            }
            None => {
            }
        }
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }

}

fn usage() {
    panic!("Usage: acl2 [sapling-spend | sapling-output | sprout | ...]");
}

// fn make_xor(cs: &mut TreeCs) -> () {
fn make_xor<CS>(mut cs: CS) -> ()
where
    CS: ConstraintSystem<bls12_381::Scalar>
{
    let x = bellman::gadgets::boolean::AllocatedBit::alloc
        (&mut cs.namespace(|| "x"), None).unwrap();
    let y = bellman::gadgets::boolean::AllocatedBit::alloc
        (&mut cs.namespace(|| "y"), None).unwrap();
    bellman::gadgets::boolean::AllocatedBit::xor
        (&mut cs.namespace(|| "z"), &x, &y).unwrap();
}

fn make_pedersen<CS>(mut cs: CS, nbits: u32) -> ()
where
    CS: ConstraintSystem<bls12_381::Scalar>
{
    let mut bits = vec![];
    for i in 0..nbits {
        let bit = bellman::gadgets::boolean::AllocatedBit::alloc
            (&mut cs.namespace(|| format!("bit{}", i)), None).unwrap();
        bits.push(bellman::gadgets::boolean::Boolean::Is(bit));
    }
    zcash_proofs::circuit::pedersen_hash::pedersen_hash
        (&mut cs,
         zcash_primitives::pedersen_hash::Personalization::NoteCommitment,
         &bits).unwrap();
}

fn make_blake2s<CS>(mut cs: CS, nbits: u32, pers: &[u8]) -> ()
where
    CS: ConstraintSystem<bls12_381::Scalar>
{
    let mut bits = vec![];
    for i in 0..nbits {
        let bit = bellman::gadgets::boolean::AllocatedBit::alloc
            (&mut cs.namespace(|| format!("bit{}", i)), None).unwrap();
        bits.push(bellman::gadgets::boolean::Boolean::Is(bit));
    }
    bellman::gadgets::blake2s::blake2s(&mut cs, &bits, &pers).unwrap();
}

fn make_ctedwards_montgomery<CS>(mut cs: CS) -> ()
where
    CS: ConstraintSystem<bls12_381::Scalar>
{
    let x = bellman::gadgets::num::AllocatedNum::alloc
        (&mut cs.namespace(|| "x"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let y = bellman::gadgets::num::AllocatedNum::alloc
        (&mut cs.namespace(|| "y"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let x = bellman::gadgets::num::Num::from(x);
    let y = bellman::gadgets::num::Num::from(y);
    let point =
        zcash_proofs::circuit::ecc::MontgomeryPoint::interpret_unchecked(x, y);
    point.into_edwards(&mut cs).unwrap();
}

fn make_montgomery_add<CS>(mut cs: CS) -> ()
where
    CS: ConstraintSystem<bls12_381::Scalar>
{
    let x1 = bellman::gadgets::num::AllocatedNum::alloc
        (&mut cs.namespace(|| "x1"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let y1 = bellman::gadgets::num::AllocatedNum::alloc
        (&mut cs.namespace(|| "y1"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let x1 = bellman::gadgets::num::Num::from(x1);
    let y1 = bellman::gadgets::num::Num::from(y1);
    let point1 =
        zcash_proofs::circuit::ecc::MontgomeryPoint::interpret_unchecked(x1, y1);
    let x2 = bellman::gadgets::num::AllocatedNum::alloc
        (&mut cs.namespace(|| "x2"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let y2 = bellman::gadgets::num::AllocatedNum::alloc
        (&mut cs.namespace(|| "y2"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let x2 = bellman::gadgets::num::Num::from(x2);
    let y2 = bellman::gadgets::num::Num::from(y2);
    let point2 =
        zcash_proofs::circuit::ecc::MontgomeryPoint::interpret_unchecked(x2, y2);
    point1.add(&mut cs, &point2).unwrap();
}

fn make_ctedwards_add<CS>(mut cs: CS) -> ()
where
    CS: ConstraintSystem<bls12_381::Scalar>
{
    let u1 = bellman::gadgets::num::AllocatedNum::alloc
        (cs.namespace(|| "u1"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let v1 = bellman::gadgets::num::AllocatedNum::alloc
        (cs.namespace(|| "v1"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let u2 = bellman::gadgets::num::AllocatedNum::alloc
        (cs.namespace(|| "u2"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let v2 = bellman::gadgets::num::AllocatedNum::alloc
        (cs.namespace(|| "v2"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let point1 = zcash_proofs::circuit::ecc::EdwardsPoint { u: u1, v: v1 };
    let point2 = zcash_proofs::circuit::ecc::EdwardsPoint { u: u2, v: v2 };
    point1.add(&mut cs, &point2).unwrap();
}

fn make_small_order<CS>(mut cs: CS) -> ()
where
    CS: ConstraintSystem<bls12_381::Scalar>
{
    let u = bellman::gadgets::num::AllocatedNum::alloc
        (cs.namespace(|| "u"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let v = bellman::gadgets::num::AllocatedNum::alloc
        (cs.namespace(|| "v"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let point = zcash_proofs::circuit::ecc::EdwardsPoint { u, v };
    point.assert_not_small_order(&mut cs).unwrap();
}

fn make_ctedwards_mul_variable<CS>(mut cs: CS) -> ()
where
    CS: ConstraintSystem<bls12_381::Scalar>
{
    let mut ks = Vec::<bellman::gadgets::boolean::Boolean>::new();
    for i in 0..251 {
        let ki = bellman::gadgets::boolean::AllocatedBit::alloc
            (&mut cs.namespace(|| format!("k{}", i)), None).unwrap();
        ks.push(bellman::gadgets::boolean::Boolean::Is(ki));
    }
    let u = bellman::gadgets::num::AllocatedNum::alloc
        (cs.namespace(|| "u"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let v = bellman::gadgets::num::AllocatedNum::alloc
        (cs.namespace(|| "v"), || Ok(bls12_381::Scalar::zero())).unwrap();
    let point = zcash_proofs::circuit::ecc::EdwardsPoint { u, v };
    point.mul(&mut cs, &ks).unwrap();
}

fn main() {
    let format = env::args().nth(1);
    let circuit = env::args().nth(2);

    let mut rcs = Acl2Cs::new();
    let mut tcs = TreeCs::new();

    let r1cs = match format.as_ref().map(|s| s.as_str()) {
        Some("r1cs") => { true }
        _ => { false }
    };

    match circuit.as_ref().map(|s| s.as_str()) {
        Some("sapling-spend") => {
            let circuit = Spend {
                value_commitment: None,
                proof_generation_key: None,
                payment_address: None,
                commitment_randomness: None,
                ar: None,
                auth_path: vec![None; 32],
                anchor: None,
            };
            if r1cs {
                circuit.synthesize(&mut rcs).unwrap();
            } else {
                circuit.synthesize(&mut tcs).unwrap();
            }
        }
        Some("sapling-output") => {
            let circuit = Output {
                value_commitment: None,
                payment_address: None,
                commitment_randomness: None,
                esk: None,
            };
            if r1cs {
                circuit.synthesize(&mut rcs).unwrap();
            } else {
                circuit.synthesize(&mut tcs).unwrap();
            }
        }
        Some("sprout") => {
            let circuit = JoinSplit {
                vpub_old: None,
                vpub_new: None,
                h_sig: None,
                phi: None,
                inputs: vec![
                    JSInput {
                        value: None,
                        a_sk: None,
                        rho: None,
                        r: None,
                        auth_path: [None; 29],
                    },
                    JSInput {
                        value: None,
                        a_sk: None,
                        rho: None,
                        r: None,
                        auth_path: [None; 29],
                    },
                ],
                outputs: vec![
                    JSOutput {
                        value: None,
                        a_pk: None,
                        r: None,
                    },
                    JSOutput {
                        value: None,
                        a_pk: None,
                        r: None,
                    },
                ],
                rt: None,
            };
            if r1cs {
                circuit.synthesize(&mut rcs).unwrap();
            } else {
                circuit.synthesize(&mut tcs).unwrap();
            }
        }
        Some("xor") => {
            if r1cs {
                make_xor(&mut rcs);
            } else {
                make_xor(&mut tcs);
            }
        }
        Some("affine-ctedwards") => {
            if r1cs {
                zcash_proofs::circuit::ecc::EdwardsPoint::witness
                    (&mut rcs, None).unwrap();
            } else {
                zcash_proofs::circuit::ecc::EdwardsPoint::witness
                    (&mut tcs, None).unwrap();
            }
        }
        Some("small-order") => {
            if r1cs {
                make_small_order(&mut rcs);
            } else {
                make_small_order(&mut tcs);
            }
        }
        Some("ctedwards-montgomery") => {
            if r1cs {
                make_ctedwards_montgomery(&mut rcs);
            } else {
                make_ctedwards_montgomery(&mut tcs);
            }
        }
        Some("montgomery-add") => {
            if r1cs {
                make_montgomery_add(&mut rcs);
            } else {
                make_montgomery_add(&mut tcs);
            }
        }
        Some("ctedwards-add") => {
            if r1cs {
                make_ctedwards_add(&mut rcs);
            } else {
                make_ctedwards_add(&mut tcs);
            }
        }
        Some("ctedwards-mul-variable") => {
            if r1cs {
                make_ctedwards_mul_variable(&mut rcs);
            } else {
                make_ctedwards_mul_variable(&mut tcs);
            }
        }
        Some("pedersen1") => {
            if r1cs {
                make_pedersen(&mut rcs, 1);
            } else {
                make_pedersen(&mut tcs, 1);
            }
        }
        Some("pedersen3") => {
            if r1cs {
                make_pedersen(&mut rcs, 3);
            } else {
                make_pedersen(&mut tcs, 3);
            }
        }
        Some("pedersen6") => {
            if r1cs {
                make_pedersen(&mut rcs, 6);
            } else {
                make_pedersen(&mut tcs, 6);
            }
        }
        Some("pedersen9") => {
            if r1cs {
                make_pedersen(&mut rcs, 9);
            } else {
                make_pedersen(&mut tcs, 9);
            }
        }
        Some("pedersen12") => {
            if r1cs {
                make_pedersen(&mut rcs, 12);
            } else {
                make_pedersen(&mut tcs, 12);
            }
        }
        Some("pedersen15") => {
            if r1cs {
                make_pedersen(&mut rcs, 15);
            } else {
                make_pedersen(&mut tcs, 15);
            }
        }
        Some("pedersen576") => {
            if r1cs {
                make_pedersen(&mut rcs, 576);
            } else {
                make_pedersen(&mut tcs, 576);
            }
        }
        Some("blake2s-nf") => {
            if r1cs {
                make_blake2s (&mut rcs, 512,
                              zcash_primitives::constants::PRF_NF_PERSONALIZATION);
            } else {
                make_blake2s (&mut tcs, 512,
                              zcash_primitives::constants::PRF_NF_PERSONALIZATION);
            }
        }
        Some("blake2s-ivk") => {
            if r1cs {
                make_blake2s (&mut rcs, 512,
                              zcash_primitives::constants::CRH_IVK_PERSONALIZATION);
            } else {
                make_blake2s (&mut tcs, 512,
                              zcash_primitives::constants::CRH_IVK_PERSONALIZATION);
            }
        }
        _ => usage(),
    }

    if r1cs {
        print!("{}", rcs);
    } else {
        print!("{}", tcs);
    }
}
