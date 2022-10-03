# Circuit Extraction

This directory contains code for extracting R1CS in ACL2 format from Rust
definitions of R1CS gadgets.  Two different formats are defined: flat R1CS and
tree-structured R1CS.  The tree-structure R1CS preserves the gadget composition
structure as defined in Rust.

## Building

As of this writing, this code was on GitHub in the
`KestrelInstitute/librustzcash` fork of the librustzcash repo,
in the branch `gen-r1cs`, as assumed by these instructions.

This procedure has been checked on MacOS 10.15.7 and Linux Mint 19.3 using
rustc 1.44.1.  If you find it does not work on a later version please submit an issue.

```
cd <path-to>/librustzcash    # go to your clone
git checkout gen-r1cs        # move to branch
git pull                     # get any latest updates
cd zcash_proofs/examples     # go to code of interest
cargo build --example acl2   # compile the Rust code
```

## Extracting R1CS

To extract a circuit, do:
```
cargo run --example acl2 <format> <circuit>
```
where `<format>` is either `r1cs` or `tree` and `<circuit>` is one of `sapling-spend`,
`sapling-output`, `sprout`, or any of the others that appear as `Some("<circuit>")` in
the file `<path-to>/librustzcash/zcash_proofs/examples/acl2.rs`.

## Example

This command:

```
cargo run --example acl2 tree montgomery-add
```

generates the tree-structured R1CS for Montgomery addition.

The generated data goes to standard output, which you can redirect to a file.

## Links

Some R1CS gadgets extracted with this tool can be found here:
https://github.com/acl2/acl2/tree/master/books/kestrel/zcash/gadgets
