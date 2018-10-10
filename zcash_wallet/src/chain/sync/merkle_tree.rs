use failure::Error;
use pairing::{
    bls12_381::{Bls12, Fr, FrRepr},
    PrimeField,
};
use sapling_crypto::primitives::Note;
use std::collections::VecDeque;
use std::iter;
use zcash_primitives::sapling::merkle_hash;
use zcash_proofs::sapling::CommitmentTreeWitness;

const SAPLING_COMMITMENT_TREE_DEPTH: usize = 32;

trait Hashable: Clone + Copy {
    /// Returns the parent node within the tree of the two given nodes.
    fn combine(&Self, &Self) -> Self;

    /// Returns a blank leaf node.
    fn blank() -> Self;
}

#[derive(Clone, Copy)]
pub struct Node {
    repr: FrRepr,
    depth: usize,
}

impl Node {
    pub fn new(repr: FrRepr) -> Self {
        Node { repr, depth: 0 }
    }
}

impl Hashable for Node {
    fn combine(lhs: &Self, rhs: &Self) -> Self {
        assert_eq!(lhs.depth, rhs.depth);
        Node {
            repr: merkle_hash(lhs.depth, &lhs.repr, &rhs.repr),
            depth: lhs.depth + 1,
        }
    }

    fn blank() -> Self {
        Node {
            repr: Note::<Bls12>::uncommitted().into_repr(),
            depth: 0,
        }
    }
}

lazy_static! {
    static ref EMPTY_ROOTS: Vec<Node> = {
        let mut v = vec![Node::blank()];
        for d in 0..SAPLING_COMMITMENT_TREE_DEPTH {
            let next = Node::combine(&v[d], &v[d]);
            v.push(next);
        }
        v
    };
}

/// A Merkle tree of Sapling note commitments.
#[derive(Clone)]
pub struct CommitmentTree {
    left: Option<Node>,
    right: Option<Node>,
    parents: Vec<Option<Node>>,
}

impl CommitmentTree {
    /// Creates an empty tree.
    pub fn new() -> Self {
        CommitmentTree {
            left: None,
            right: None,
            parents: vec![],
        }
    }

    /// Returns the number of notes in the tree.
    pub fn size(&self) -> usize {
        self.parents.iter().enumerate().fold(
            match (self.left.is_some(), self.right.is_some()) {
                (false, false) => 0,
                (true, false) | (false, true) => 1,
                (true, true) => 2,
            },
            |acc, (i, p)| {
                // Treat occupation of parents array as a binary number
                // (right-shifted by 1)
                acc + if p.is_some() { 1 << (i + 1) } else { 0 }
            },
        )
    }

    fn is_complete(&self, depth: usize) -> bool {
        self.left.is_some()
            && self.right.is_some()
            && self.parents.len() == depth - 1
            && self.parents.iter().fold(true, |acc, p| acc && p.is_some())
    }

    /// Adds a note to the tree. Returns an error if the tree is full.
    pub fn append(&mut self, node: Node) -> Result<(), Error> {
        self.append_inner(node, SAPLING_COMMITMENT_TREE_DEPTH)
    }

    fn append_inner(&mut self, node: Node, depth: usize) -> Result<(), Error> {
        if self.is_complete(depth) {
            return Err(format_err!("Tree is full"));
        }

        match (self.left, self.right) {
            (None, _) => self.left = Some(node),
            (_, None) => self.right = Some(node),
            (Some(l), Some(r)) => {
                let mut combined = Node::combine(&l, &r);
                self.left = Some(node);
                self.right = None;

                for i in 0..depth {
                    if i < self.parents.len() {
                        if let Some(p) = self.parents[i] {
                            combined = Node::combine(&p, &combined);
                            self.parents[i] = None;
                        } else {
                            self.parents[i] = Some(combined);
                            break;
                        }
                    } else {
                        self.parents.push(Some(combined));
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    /// Returns the current root of the tree.
    pub fn root(&self) -> Node {
        self.root_inner(SAPLING_COMMITMENT_TREE_DEPTH)
    }

    fn root_inner(&self, depth: usize) -> Node {
        assert!(depth > 0);

        // 1) Hash left and right leaves together.
        //    - Empty leaves are used as needed.
        let leaf_root = Node::combine(
            &match self.left {
                Some(node) => node,
                None => EMPTY_ROOTS[0],
            },
            &match self.right {
                Some(node) => node,
                None => EMPTY_ROOTS[0],
            },
        );

        // 2) Hash in parents up to the currently-filled depth.
        //    - Roots of the empty subtrees are used as needed.
        let mid_root = self
            .parents
            .iter()
            .enumerate()
            .fold(leaf_root, |root, (i, p)| match p {
                Some(node) => Node::combine(node, &root),
                None => Node::combine(&root, &EMPTY_ROOTS[i + 1]),
            });

        // 3) Hash in roots of the empty subtrees up to the final depth.
        ((self.parents.len() + 1)..depth)
            .fold(mid_root, |root, d| Node::combine(&root, &EMPTY_ROOTS[d]))
    }
}

struct PathFiller {
    queue: VecDeque<Node>,
}

impl PathFiller {
    fn next(&mut self, depth: usize) -> Node {
        self.queue.pop_front().unwrap_or_else(|| EMPTY_ROOTS[depth])
    }
}

pub struct IncrementalWitness {
    tree: CommitmentTree,
    filled: Vec<Node>,
    cursor_depth: usize,
    cursor: Option<CommitmentTree>,
}

impl IncrementalWitness {
    pub fn from_tree(tree: &CommitmentTree) -> IncrementalWitness {
        IncrementalWitness {
            tree: tree.clone(),
            filled: vec![],
            cursor_depth: 0,
            cursor: None,
        }
    }

    /// Returns the position of the witnessed note in the commitment tree.
    pub fn position(&self) -> usize {
        self.tree.size() - 1
    }

    /// Finds the next "depth" of an unfilled subtree.
    fn next_depth(&self) -> usize {
        let mut skip = self.filled.len();

        if self.tree.left.is_none() {
            if skip > 0 {
                skip -= 1;
            } else {
                return 0;
            }
        }

        if self.tree.right.is_none() {
            if skip > 0 {
                skip -= 1;
            } else {
                return 0;
            }
        }

        let mut d = 1;
        for p in &self.tree.parents {
            if p.is_none() {
                if skip > 0 {
                    skip -= 1;
                } else {
                    return d;
                }
            }
            d += 1;
        }

        d + skip
    }

    /// Tracks a note that has been added to the underlying tree. Returns an
    /// error if the tree is full.
    pub fn append(&mut self, node: Node) -> Result<(), Error> {
        self.append_inner(node, SAPLING_COMMITMENT_TREE_DEPTH)
    }

    fn append_inner(&mut self, node: Node, depth: usize) -> Result<(), Error> {
        if let Some(mut cursor) = self.cursor.take() {
            cursor
                .append_inner(node, depth)
                .expect("cursor should not be full");
            if cursor.is_complete(self.cursor_depth) {
                self.filled.push(cursor.root_inner(self.cursor_depth));
            } else {
                self.cursor = Some(cursor);
            }
        } else {
            self.cursor_depth = self.next_depth();
            if self.cursor_depth >= depth {
                return Err(format_err!("Tree is full"));
            }

            if self.cursor_depth == 0 {
                self.filled.push(node);
            } else {
                let mut cursor = CommitmentTree::new();
                cursor
                    .append_inner(node, depth)
                    .expect("cursor should not be full");
                self.cursor = Some(cursor);
            }
        }

        Ok(())
    }

    /// Returns the current witness.
    pub fn path(&self) -> Result<CommitmentTreeWitness, Error> {
        self.path_inner(SAPLING_COMMITMENT_TREE_DEPTH)
    }

    fn path_inner(&self, depth: usize) -> Result<CommitmentTreeWitness, Error> {
        let cursor_root = self
            .cursor
            .as_ref()
            .map(|c| c.root_inner(self.cursor_depth));
        let queue = if let Some(node) = cursor_root {
            self.filled
                .iter()
                .cloned()
                .chain(iter::once(node))
                .collect()
        } else {
            self.filled.iter().cloned().collect()
        };
        let mut filler = PathFiller { queue };

        let mut auth_path = Vec::new();

        if let Some(node) = self.tree.left {
            if self.tree.right.is_some() {
                auth_path.push(Some((node, true)));
            } else {
                auth_path.push(Some((filler.next(0), false)));
            }
        } else {
            return Err(format_err!(
                "Can't create an authentication path for the beginning of the tree"
            ));
        }

        for (i, p) in self.tree.parents.iter().enumerate() {
            auth_path.push(match p {
                Some(node) => Some((*node, true)),
                None => Some((filler.next(i + 1), false)),
            });
        }

        for i in self.tree.parents.len()..(depth - 1) {
            auth_path.push(Some((filler.next(i + 1), false)));
        }
        assert_eq!(auth_path.len(), depth);

        Ok(CommitmentTreeWitness::from_path(
            auth_path
                .iter()
                .map(|n| {
                    n.map(|(node, b)| {
                        (
                            Fr::from_repr(node.repr)
                                .expect("All nodes in the tree should be in the prime field"),
                            b,
                        )
                    })
                }).collect(),
            self.position() as u64,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::{CommitmentTree, Hashable, IncrementalWitness, Node, EMPTY_ROOTS};

    use failure::Error;
    use hex;
    use pairing::{bls12_381::FrRepr, PrimeFieldRepr};
    use sapling_crypto::primitives::Note;
    use zcash_proofs::sapling::CommitmentTreeWitness;

    const HEX_EMPTY_ROOTS: [&str; 33] = [
        "0100000000000000000000000000000000000000000000000000000000000000",
        "817de36ab2d57feb077634bca77819c8e0bd298c04f6fed0e6a83cc1356ca155",
        "ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e34",
        "d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c",
        "e110de65c907b9dea4ae0bd83a4b0a51bea175646a64c12b4c9f931b2cb31b49",
        "912d82b2c2bca231f71efcf61737fbf0a08befa0416215aeef53e8bb6d23390a",
        "8ac9cf9c391e3fd42891d27238a81a8a5c1d3a72b1bcbea8cf44a58ce7389613",
        "d6c639ac24b46bd19341c91b13fdcab31581ddaf7f1411336a271f3d0aa52813",
        "7b99abdc3730991cc9274727d7d82d28cb794edbc7034b4f0053ff7c4b680444",
        "43ff5457f13b926b61df552d4e402ee6dc1463f99a535f9a713439264d5b616b",
        "ba49b659fbd0b7334211ea6a9d9df185c757e70aa81da562fb912b84f49bce72",
        "4777c8776a3b1e69b73a62fa701fa4f7a6282d9aee2c7a6b82e7937d7081c23c",
        "ec677114c27206f5debc1c1ed66f95e2b1885da5b7be3d736b1de98579473048",
        "1b77dac4d24fb7258c3c528704c59430b630718bec486421837021cf75dab651",
        "bd74b25aacb92378a871bf27d225cfc26baca344a1ea35fdd94510f3d157082c",
        "d6acdedf95f608e09fa53fb43dcd0990475726c5131210c9e5caeab97f0e642f",
        "1ea6675f9551eeb9dfaaa9247bc9858270d3d3a4c5afa7177a984d5ed1be2451",
        "6edb16d01907b759977d7650dad7e3ec049af1a3d875380b697c862c9ec5d51c",
        "cd1c8dbf6e3acc7a80439bc4962cf25b9dce7c896f3a5bd70803fc5a0e33cf00",
        "6aca8448d8263e547d5ff2950e2ed3839e998d31cbc6ac9fd57bc6002b159216",
        "8d5fa43e5a10d11605ac7430ba1f5d81fb1b68d29a640405767749e841527673",
        "08eeab0c13abd6069e6310197bf80f9c1ea6de78fd19cbae24d4a520e6cf3023",
        "0769557bc682b1bf308646fd0b22e648e8b9e98f57e29f5af40f6edb833e2c49",
        "4c6937d78f42685f84b43ad3b7b00f81285662f85c6a68ef11d62ad1a3ee0850",
        "fee0e52802cb0c46b1eb4d376c62697f4759f6c8917fa352571202fd778fd712",
        "16d6252968971a83da8521d65382e61f0176646d771c91528e3276ee45383e4a",
        "d2e1642c9a462229289e5b0e3b7f9008e0301cbb93385ee0e21da2545073cb58",
        "a5122c08ff9c161d9ca6fc462073396c7d7d38e8ee48cdb3bea7e2230134ed6a",
        "28e7b841dcbc47cceb69d7cb8d94245fb7cb2ba3a7a6bc18f13f945f7dbd6e2a",
        "e1f34b034d4a3cd28557e2907ebf990c918f64ecb50a94f01d6fda5ca5c7ef72",
        "12935f14b676509b81eb49ef25f39269ed72309238b4c145803544b646dca62d",
        "b2eed031d4d6a4f02a097f80b54cc1541d4163c6b6f5971f88b6e41d35c53814",
        "fbc2f4300c01f0b7820d00e3347c8da4ee614674376cbc45359daa54f9b5493e",
    ];

    const TESTING_DEPTH: usize = 4;

    struct TestCommitmentTree(CommitmentTree);

    impl TestCommitmentTree {
        fn new() -> Self {
            TestCommitmentTree(CommitmentTree::new())
        }

        fn size(&self) -> usize {
            self.0.size()
        }

        fn append(&mut self, node: Node) -> Result<(), Error> {
            self.0.append_inner(node, TESTING_DEPTH)
        }

        fn root(&self) -> Node {
            self.0.root_inner(TESTING_DEPTH)
        }
    }

    struct TestIncrementalWitness(IncrementalWitness);

    impl TestIncrementalWitness {
        fn from_tree(tree: &TestCommitmentTree) -> Self {
            TestIncrementalWitness(IncrementalWitness::from_tree(&tree.0))
        }

        fn append(&mut self, node: Node) -> Result<(), Error> {
            self.0.append_inner(node, TESTING_DEPTH)
        }

        fn path(&self) -> Result<CommitmentTreeWitness, Error> {
            self.0.path_inner(TESTING_DEPTH)
        }
    }

    #[test]
    fn empty_root_test_vectors() {
        let mut tmp = [0u8; 32];
        for i in 0..HEX_EMPTY_ROOTS.len() {
            EMPTY_ROOTS[i]
                .repr
                .write_le(&mut tmp[..])
                .expect("length is 32 bytes");
            assert_eq!(hex::encode(tmp), HEX_EMPTY_ROOTS[i]);
        }
    }

    #[test]
    fn sapling_empty_root() {
        let mut tmp = [0u8; 32];
        CommitmentTree::new()
            .root()
            .repr
            .write_le(&mut tmp[..])
            .expect("length is 32 bytes");
        assert_eq!(
            hex::encode(tmp),
            "fbc2f4300c01f0b7820d00e3347c8da4ee614674376cbc45359daa54f9b5493e"
        );
    }

    #[test]
    fn empty_commitment_tree_roots() {
        let tree = CommitmentTree::new();
        let mut tmp = [0u8; 32];
        for i in 1..HEX_EMPTY_ROOTS.len() {
            tree.root_inner(i)
                .repr
                .write_le(&mut tmp[..])
                .expect("length is 32 bytes");
            assert_eq!(hex::encode(tmp), HEX_EMPTY_ROOTS[i]);
        }
    }

    #[test]
    fn test_sapling_tree() {
        // From https://github.com/zcash/zcash/blob/master/src/test/data/merkle_commitments_sapling.json
        // Byte-reversed because the original test vectors are loaded using uint256S()
        let commitments = [
            "b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f55",
            "225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b11458",
            "7c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c",
            "50421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a030",
            "aaec63863aaa0b2e3b8009429bdddd455e59be6f40ccab887a32eb98723efc12",
            "f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a02",
            "bc8a5ec71647415c380203b681f7717366f3501661512225b6dc3e121efc0b2e",
            "da1adda2ccde9381e11151686c121e7f52d19a990439161c7eb5a9f94be5a511",
            "3a27fed5dbbc475d3880360e38638c882fd9b273b618fc433106896083f77446",
            "c7ca8f7df8fd997931d33985d935ee2d696856cc09cc516d419ea6365f163008",
            "f0fa37e8063b139d342246142fc48e7c0c50d0a62c97768589e06466742c3702",
            "e6d4d7685894d01b32f7e081ab188930be6c2b9f76d6847b7f382e3dddd7c608",
            "8cebb73be883466d18d3b0c06990520e80b936440a2c9fd184d92a1f06c4e826",
            "22fab8bcdb88154dbf5877ad1e2d7f1b541bc8a5ec1b52266095381339c27c03",
            "f43e3aac61e5a753062d4d0508c26ceaf5e4c0c58ba3c956e104b5d2cf67c41c",
            "3a3661bc12b72646c94bc6c92796e81953985ee62d80a9ec3645a9a95740ac15",
        ];

        // From https://github.com/zcash/zcash/blob/master/src/test/data/merkle_roots_sapling.json
        let roots = [
            "8c3daa300c9710bf24d2595536e7c80ff8d147faca726636d28e8683a0c27703",
            "8611f17378eb55e8c3c3f0a5f002e2b0a7ca39442fc928322b8072d1079c213d",
            "3db73b998d536be0e1c2ec124df8e0f383ae7b602968ff6a5276ca0695023c46",
            "7ac2e6442fec5970e116dfa4f2ee606f395366cafb1fa7dfd6c3de3ce18c4363",
            "6a8f11ab2a11c262e39ed4ea3825ae6c94739ccf94479cb69402c5722b034532",
            "149595eed0b54a7e694cc8a68372525b9ae2c7b102514f527460db91eb690565",
            "8c0432f1994a2381a7a4b5fda770336011f9e0b30784f9a5597901619c797045",
            "e780c48d70420601f3313ff8488d7766b70c059c53aa3cda2ff1ef57ff62383c",
            "f919f03caaed8a2c60f58c0d43838f83e670dc7e8ccd25daa04a13f3e8f45541",
            "74f32b36629724038e71cbd6823b5a666440205a7d1a9242e95870b53d81f34a",
            "a4af205a4e1ee02102866b23a68930ac33efda9235832f49b17fcc4939be4525",
            "a946a42f1636045a16e65b2308e036d9da70089686c87c692e45912bd1cab772",
            "a1db2dbac055364c1cb43cbeb49c7e2815bff855122602a2ad0fb981a91e0e39",
            "16329b3ba4f0640f4d306532d9ea6ba0fbf0e70e44ed57d27b4277ed9cda6849",
            "7b6523b2d9b23f72fec6234aa6a1f8fae3dba1c6a266023ea8b1826feba7a25c",
            "5c0bea7e17bde5bee4eb795c2eec3d389a68da587b36dd687b134826ecc09308",
        ];

        // From https://github.com/zcash/zcash/blob/master/src/test/data/merkle_path_sapling.json
        let paths = [
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e3420817de36ab2d57feb077634bca77819c8e0bd298c04f6fed0e6a83cc1356ca15520225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e342037b3a0921a4047e617bde62b8958f86c010e6af6cc650959b9f50af8c7e8392620225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e342037b3a0921a4047e617bde62b8958f86c010e6af6cc650959b9f50af8c7e8392620b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e3420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e3420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e342062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c2031d39685384e4ea322594d99a15aa8bdd8cc5cd6724410fa385b8d5447f1740220f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c2031d39685384e4ea322594d99a15aa8bdd8cc5cd6724410fa385b8d5447f1740220f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c2031d39685384e4ea322594d99a15aa8bdd8cc5cd6724410fa385b8d5447f174022062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c2031d39685384e4ea322594d99a15aa8bdd8cc5cd6724410fa385b8d5447f174022062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20f0321eea8e13c2f3a567f894c9738759d9d01e64ec259caf2cecca61374c157320f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20f0321eea8e13c2f3a567f894c9738759d9d01e64ec259caf2cecca61374c157320f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20f0321eea8e13c2f3a567f894c9738759d9d01e64ec259caf2cecca61374c15732062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20f0321eea8e13c2f3a567f894c9738759d9d01e64ec259caf2cecca61374c15732062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420817de36ab2d57feb077634bca77819c8e0bd298c04f6fed0e6a83cc1356ca15520f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a020400000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c2082c424de0185a63f6ce0aa65d3d55890748af44bb4bb5822a9a21df34546d32220f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c2082c424de0185a63f6ce0aa65d3d55890748af44bb4bb5822a9a21df34546d32220f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c2082c424de0185a63f6ce0aa65d3d55890748af44bb4bb5822a9a21df34546d3222062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c2082c424de0185a63f6ce0aa65d3d55890748af44bb4bb5822a9a21df34546d3222062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f655186564206ab2e08286c36f6fe4374baebdc28b97e2f1f4ea3544fafd8a6489f42824bf0e20f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a020400000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f655186564206ab2e08286c36f6fe4374baebdc28b97e2f1f4ea3544fafd8a6489f42824bf0e20aaec63863aaa0b2e3b8009429bdddd455e59be6f40ccab887a32eb98723efc120500000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a020400000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20aaec63863aaa0b2e3b8009429bdddd455e59be6f40ccab887a32eb98723efc120500000000000000",
            "0420d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420da1adda2ccde9381e11151686c121e7f52d19a990439161c7eb5a9f94be5a5110600000000000000",
            "0420109713c6c346ab0b17904ae18d101d92a98a612116a3f787043c802b55d5573120130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "0420109713c6c346ab0b17904ae18d101d92a98a612116a3f787043c802b55d5573120130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "0420109713c6c346ab0b17904ae18d101d92a98a612116a3f787043c802b55d5573120130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "0420109713c6c346ab0b17904ae18d101d92a98a612116a3f787043c802b55d5573120130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "0420109713c6c346ab0b17904ae18d101d92a98a612116a3f787043c802b55d55731201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a020400000000000000",
            "0420109713c6c346ab0b17904ae18d101d92a98a612116a3f787043c802b55d55731201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20aaec63863aaa0b2e3b8009429bdddd455e59be6f40ccab887a32eb98723efc120500000000000000",
            "0420109713c6c346ab0b17904ae18d101d92a98a612116a3f787043c802b55d55731201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420da1adda2ccde9381e11151686c121e7f52d19a990439161c7eb5a9f94be5a5110600000000000000",
            "0420109713c6c346ab0b17904ae18d101d92a98a612116a3f787043c802b55d55731201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420bc8a5ec71647415c380203b681f7717366f3501661512225b6dc3e121efc0b2e0700000000000000",
            "0420bced38e720c8eab9b3b8b2959e5a8b8dda2b2537f6ea71c8e2aea8834a9af54220130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "0420bced38e720c8eab9b3b8b2959e5a8b8dda2b2537f6ea71c8e2aea8834a9af54220130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "0420bced38e720c8eab9b3b8b2959e5a8b8dda2b2537f6ea71c8e2aea8834a9af54220130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "0420bced38e720c8eab9b3b8b2959e5a8b8dda2b2537f6ea71c8e2aea8834a9af54220130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "0420bced38e720c8eab9b3b8b2959e5a8b8dda2b2537f6ea71c8e2aea8834a9af542201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a020400000000000000",
            "0420bced38e720c8eab9b3b8b2959e5a8b8dda2b2537f6ea71c8e2aea8834a9af542201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20aaec63863aaa0b2e3b8009429bdddd455e59be6f40ccab887a32eb98723efc120500000000000000",
            "0420bced38e720c8eab9b3b8b2959e5a8b8dda2b2537f6ea71c8e2aea8834a9af542201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420da1adda2ccde9381e11151686c121e7f52d19a990439161c7eb5a9f94be5a5110600000000000000",
            "0420bced38e720c8eab9b3b8b2959e5a8b8dda2b2537f6ea71c8e2aea8834a9af542201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420bc8a5ec71647415c380203b681f7717366f3501661512225b6dc3e121efc0b2e0700000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e3420817de36ab2d57feb077634bca77819c8e0bd298c04f6fed0e6a83cc1356ca15520c7ca8f7df8fd997931d33985d935ee2d696856cc09cc516d419ea6365f1630080800000000000000",
            "042094d3061a43d999e95bab82684aeb53d0a381b40e33a80abfc5c05e25b0a91d0f20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "042094d3061a43d999e95bab82684aeb53d0a381b40e33a80abfc5c05e25b0a91d0f20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "042094d3061a43d999e95bab82684aeb53d0a381b40e33a80abfc5c05e25b0a91d0f20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "042094d3061a43d999e95bab82684aeb53d0a381b40e33a80abfc5c05e25b0a91d0f20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "042094d3061a43d999e95bab82684aeb53d0a381b40e33a80abfc5c05e25b0a91d0f201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a020400000000000000",
            "042094d3061a43d999e95bab82684aeb53d0a381b40e33a80abfc5c05e25b0a91d0f201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20aaec63863aaa0b2e3b8009429bdddd455e59be6f40ccab887a32eb98723efc120500000000000000",
            "042094d3061a43d999e95bab82684aeb53d0a381b40e33a80abfc5c05e25b0a91d0f201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420da1adda2ccde9381e11151686c121e7f52d19a990439161c7eb5a9f94be5a5110600000000000000",
            "042094d3061a43d999e95bab82684aeb53d0a381b40e33a80abfc5c05e25b0a91d0f201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420bc8a5ec71647415c380203b681f7717366f3501661512225b6dc3e121efc0b2e0700000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e342076bd791f7708c0b6f5a348d574032e07ce3b1929daae19530346f5de955d543c20c7ca8f7df8fd997931d33985d935ee2d696856cc09cc516d419ea6365f1630080800000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e342076bd791f7708c0b6f5a348d574032e07ce3b1929daae19530346f5de955d543c203a27fed5dbbc475d3880360e38638c882fd9b273b618fc433106896083f774460900000000000000",
            "042061ae87cb694e8237accda801c8271a8a9d4ffc2581aebf923f5227f24c6bb92a20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "042061ae87cb694e8237accda801c8271a8a9d4ffc2581aebf923f5227f24c6bb92a20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "042061ae87cb694e8237accda801c8271a8a9d4ffc2581aebf923f5227f24c6bb92a20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "042061ae87cb694e8237accda801c8271a8a9d4ffc2581aebf923f5227f24c6bb92a20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "042061ae87cb694e8237accda801c8271a8a9d4ffc2581aebf923f5227f24c6bb92a201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a020400000000000000",
            "042061ae87cb694e8237accda801c8271a8a9d4ffc2581aebf923f5227f24c6bb92a201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20aaec63863aaa0b2e3b8009429bdddd455e59be6f40ccab887a32eb98723efc120500000000000000",
            "042061ae87cb694e8237accda801c8271a8a9d4ffc2581aebf923f5227f24c6bb92a201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420da1adda2ccde9381e11151686c121e7f52d19a990439161c7eb5a9f94be5a5110600000000000000",
            "042061ae87cb694e8237accda801c8271a8a9d4ffc2581aebf923f5227f24c6bb92a201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420bc8a5ec71647415c380203b681f7717366f3501661512225b6dc3e121efc0b2e0700000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e3420635c0b1b8035705127dc3f672191b4958ad331f9134117e3ba7d721f712b614420c7ca8f7df8fd997931d33985d935ee2d696856cc09cc516d419ea6365f1630080800000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e3420635c0b1b8035705127dc3f672191b4958ad331f9134117e3ba7d721f712b6144203a27fed5dbbc475d3880360e38638c882fd9b273b618fc433106896083f774460900000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e3420cca46d2249e0d79669b8ad2e8c3fc5e67a8501112aa4e572fe03a1868ef3173220e6d4d7685894d01b32f7e081ab188930be6c2b9f76d6847b7f382e3dddd7c6080a00000000000000",
            "04208850438b439403c52a62aa6c81280ce5ea92bc5ff899ada6933c6afddc882e1820130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "04208850438b439403c52a62aa6c81280ce5ea92bc5ff899ada6933c6afddc882e1820130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "04208850438b439403c52a62aa6c81280ce5ea92bc5ff899ada6933c6afddc882e1820130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "04208850438b439403c52a62aa6c81280ce5ea92bc5ff899ada6933c6afddc882e1820130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "04208850438b439403c52a62aa6c81280ce5ea92bc5ff899ada6933c6afddc882e18201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a020400000000000000",
            "04208850438b439403c52a62aa6c81280ce5ea92bc5ff899ada6933c6afddc882e18201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20aaec63863aaa0b2e3b8009429bdddd455e59be6f40ccab887a32eb98723efc120500000000000000",
            "04208850438b439403c52a62aa6c81280ce5ea92bc5ff899ada6933c6afddc882e18201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420da1adda2ccde9381e11151686c121e7f52d19a990439161c7eb5a9f94be5a5110600000000000000",
            "04208850438b439403c52a62aa6c81280ce5ea92bc5ff899ada6933c6afddc882e18201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420bc8a5ec71647415c380203b681f7717366f3501661512225b6dc3e121efc0b2e0700000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20130266c8ace013b416e56be57600a9da16e136df92231a964613e2885cce756620635c0b1b8035705127dc3f672191b4958ad331f9134117e3ba7d721f712b614420c7ca8f7df8fd997931d33985d935ee2d696856cc09cc516d419ea6365f1630080800000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20130266c8ace013b416e56be57600a9da16e136df92231a964613e2885cce756620635c0b1b8035705127dc3f672191b4958ad331f9134117e3ba7d721f712b6144203a27fed5dbbc475d3880360e38638c882fd9b273b618fc433106896083f774460900000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20130266c8ace013b416e56be57600a9da16e136df92231a964613e2885cce756620cca46d2249e0d79669b8ad2e8c3fc5e67a8501112aa4e572fe03a1868ef3173220e6d4d7685894d01b32f7e081ab188930be6c2b9f76d6847b7f382e3dddd7c6080a00000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20130266c8ace013b416e56be57600a9da16e136df92231a964613e2885cce756620cca46d2249e0d79669b8ad2e8c3fc5e67a8501112aa4e572fe03a1868ef3173220f0fa37e8063b139d342246142fc48e7c0c50d0a62c97768589e06466742c37020b00000000000000",
            "0420c9cd5269cd697706cb0745d57f66e5ba4a5051fb910127318d283f751910ac7120130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "0420c9cd5269cd697706cb0745d57f66e5ba4a5051fb910127318d283f751910ac7120130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "0420c9cd5269cd697706cb0745d57f66e5ba4a5051fb910127318d283f751910ac7120130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "0420c9cd5269cd697706cb0745d57f66e5ba4a5051fb910127318d283f751910ac7120130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "0420c9cd5269cd697706cb0745d57f66e5ba4a5051fb910127318d283f751910ac71201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a020400000000000000",
            "0420c9cd5269cd697706cb0745d57f66e5ba4a5051fb910127318d283f751910ac71201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20aaec63863aaa0b2e3b8009429bdddd455e59be6f40ccab887a32eb98723efc120500000000000000",
            "0420c9cd5269cd697706cb0745d57f66e5ba4a5051fb910127318d283f751910ac71201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420da1adda2ccde9381e11151686c121e7f52d19a990439161c7eb5a9f94be5a5110600000000000000",
            "0420c9cd5269cd697706cb0745d57f66e5ba4a5051fb910127318d283f751910ac71201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420bc8a5ec71647415c380203b681f7717366f3501661512225b6dc3e121efc0b2e0700000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20c2b786e4ab72ae4f01c7241bc056817b19d42bc85107f42c3fd3a9b9e98f156420635c0b1b8035705127dc3f672191b4958ad331f9134117e3ba7d721f712b614420c7ca8f7df8fd997931d33985d935ee2d696856cc09cc516d419ea6365f1630080800000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20c2b786e4ab72ae4f01c7241bc056817b19d42bc85107f42c3fd3a9b9e98f156420635c0b1b8035705127dc3f672191b4958ad331f9134117e3ba7d721f712b6144203a27fed5dbbc475d3880360e38638c882fd9b273b618fc433106896083f774460900000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20c2b786e4ab72ae4f01c7241bc056817b19d42bc85107f42c3fd3a9b9e98f156420cca46d2249e0d79669b8ad2e8c3fc5e67a8501112aa4e572fe03a1868ef3173220e6d4d7685894d01b32f7e081ab188930be6c2b9f76d6847b7f382e3dddd7c6080a00000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20c2b786e4ab72ae4f01c7241bc056817b19d42bc85107f42c3fd3a9b9e98f156420cca46d2249e0d79669b8ad2e8c3fc5e67a8501112aa4e572fe03a1868ef3173220f0fa37e8063b139d342246142fc48e7c0c50d0a62c97768589e06466742c37020b00000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20002df68503da9247dfde6585cb8c9fa94897cf21735f8fc1b32116ef474de05c20817de36ab2d57feb077634bca77819c8e0bd298c04f6fed0e6a83cc1356ca1552022fab8bcdb88154dbf5877ad1e2d7f1b541bc8a5ec1b52266095381339c27c030c00000000000000",
            "04203cf9ea50bea2cebf829213d91c098813d11dbe5c6696cdaefab3249dbf892f5e20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "04203cf9ea50bea2cebf829213d91c098813d11dbe5c6696cdaefab3249dbf892f5e20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "04203cf9ea50bea2cebf829213d91c098813d11dbe5c6696cdaefab3249dbf892f5e20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "04203cf9ea50bea2cebf829213d91c098813d11dbe5c6696cdaefab3249dbf892f5e20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "04203cf9ea50bea2cebf829213d91c098813d11dbe5c6696cdaefab3249dbf892f5e201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a020400000000000000",
            "04203cf9ea50bea2cebf829213d91c098813d11dbe5c6696cdaefab3249dbf892f5e201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20aaec63863aaa0b2e3b8009429bdddd455e59be6f40ccab887a32eb98723efc120500000000000000",
            "04203cf9ea50bea2cebf829213d91c098813d11dbe5c6696cdaefab3249dbf892f5e201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420da1adda2ccde9381e11151686c121e7f52d19a990439161c7eb5a9f94be5a5110600000000000000",
            "04203cf9ea50bea2cebf829213d91c098813d11dbe5c6696cdaefab3249dbf892f5e201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420bc8a5ec71647415c380203b681f7717366f3501661512225b6dc3e121efc0b2e0700000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20cd6db4bcd77d6ca695b9579f9ec5791d106f83b69118bb3a2a2a99f63779e06720635c0b1b8035705127dc3f672191b4958ad331f9134117e3ba7d721f712b614420c7ca8f7df8fd997931d33985d935ee2d696856cc09cc516d419ea6365f1630080800000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20cd6db4bcd77d6ca695b9579f9ec5791d106f83b69118bb3a2a2a99f63779e06720635c0b1b8035705127dc3f672191b4958ad331f9134117e3ba7d721f712b6144203a27fed5dbbc475d3880360e38638c882fd9b273b618fc433106896083f774460900000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20cd6db4bcd77d6ca695b9579f9ec5791d106f83b69118bb3a2a2a99f63779e06720cca46d2249e0d79669b8ad2e8c3fc5e67a8501112aa4e572fe03a1868ef3173220e6d4d7685894d01b32f7e081ab188930be6c2b9f76d6847b7f382e3dddd7c6080a00000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20cd6db4bcd77d6ca695b9579f9ec5791d106f83b69118bb3a2a2a99f63779e06720cca46d2249e0d79669b8ad2e8c3fc5e67a8501112aa4e572fe03a1868ef3173220f0fa37e8063b139d342246142fc48e7c0c50d0a62c97768589e06466742c37020b00000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20002df68503da9247dfde6585cb8c9fa94897cf21735f8fc1b32116ef474de05c2045d573e80606a552974215e13b5d3e7b4dd8675c77b8d612d293475ee139b9472022fab8bcdb88154dbf5877ad1e2d7f1b541bc8a5ec1b52266095381339c27c030c00000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20002df68503da9247dfde6585cb8c9fa94897cf21735f8fc1b32116ef474de05c2045d573e80606a552974215e13b5d3e7b4dd8675c77b8d612d293475ee139b947208cebb73be883466d18d3b0c06990520e80b936440a2c9fd184d92a1f06c4e8260d00000000000000",
            "04201d73ff8e39cff60ff0d6402cc752a3351f1b434dccfa1941da3b1e422b73a33c20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420225747f3b5d5dab4e5a424f81f85c904ff43286e0f3fd07ef0b8c6a627b114580000000000000000",
            "04201d73ff8e39cff60ff0d6402cc752a3351f1b434dccfa1941da3b1e422b73a33c20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f2420f2c6ff34520c4ed63159b5ad4e99712fe64e3b4add73c66218e9797ac15a826420b02310f2e087e55bfd07ef5e242e3b87ee5d00c9ab52f61e6bd42542f93a6f550100000000000000",
            "04201d73ff8e39cff60ff0d6402cc752a3351f1b434dccfa1941da3b1e422b73a33c20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e6662050421d6c2c94571dfaaa135a4ff15bf916681ebd62c0e43e69e3b90684d0a0300200000000000000",
            "04201d73ff8e39cff60ff0d6402cc752a3351f1b434dccfa1941da3b1e422b73a33c20130adab3afe0931c42f058efb1381c2dce6cc768ad7964330146bf88b2b34f242062324ff2c329e99193a74d28a585a3c167a93bf41a255135529c913bd9b1e666207c3ea01a6e3a3d90cf59cd789e467044b5cd78eb2c84cc6816f960746d0e036c0300000000000000",
            "04201d73ff8e39cff60ff0d6402cc752a3351f1b434dccfa1941da3b1e422b73a33c201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20f76748d40d5ee5f9a608512e7954dd515f86e8f6d009141c89163de1cf351a020400000000000000",
            "04201d73ff8e39cff60ff0d6402cc752a3351f1b434dccfa1941da3b1e422b73a33c201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420d0c26e22b78df58552b4fd61e8883a70f9011556b2e14b80ff23c591db7dbc4c20aaec63863aaa0b2e3b8009429bdddd455e59be6f40ccab887a32eb98723efc120500000000000000",
            "04201d73ff8e39cff60ff0d6402cc752a3351f1b434dccfa1941da3b1e422b73a33c201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420da1adda2ccde9381e11151686c121e7f52d19a990439161c7eb5a9f94be5a5110600000000000000",
            "04201d73ff8e39cff60ff0d6402cc752a3351f1b434dccfa1941da3b1e422b73a33c201fb189b02ad2f7c6b0d09bd5691c4896c28269da3d4ba768b1b446f65518656420eb97b35d826f55a65e23ea7febf38fadea8517312ca79346c129a277260fd72420bc8a5ec71647415c380203b681f7717366f3501661512225b6dc3e121efc0b2e0700000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20076795f3651049c8895a7d127eb9bb4a17698da400430b33fdd06b1d8160394020635c0b1b8035705127dc3f672191b4958ad331f9134117e3ba7d721f712b614420c7ca8f7df8fd997931d33985d935ee2d696856cc09cc516d419ea6365f1630080800000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20076795f3651049c8895a7d127eb9bb4a17698da400430b33fdd06b1d8160394020635c0b1b8035705127dc3f672191b4958ad331f9134117e3ba7d721f712b6144203a27fed5dbbc475d3880360e38638c882fd9b273b618fc433106896083f774460900000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20076795f3651049c8895a7d127eb9bb4a17698da400430b33fdd06b1d8160394020cca46d2249e0d79669b8ad2e8c3fc5e67a8501112aa4e572fe03a1868ef3173220e6d4d7685894d01b32f7e081ab188930be6c2b9f76d6847b7f382e3dddd7c6080a00000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20076795f3651049c8895a7d127eb9bb4a17698da400430b33fdd06b1d8160394020cca46d2249e0d79669b8ad2e8c3fc5e67a8501112aa4e572fe03a1868ef3173220f0fa37e8063b139d342246142fc48e7c0c50d0a62c97768589e06466742c37020b00000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20002df68503da9247dfde6585cb8c9fa94897cf21735f8fc1b32116ef474de05c20afa80a9a1bb8b6aad144cfb53e0bab004dd541c8b72025ae694bb60d6050a5322022fab8bcdb88154dbf5877ad1e2d7f1b541bc8a5ec1b52266095381339c27c030c00000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20002df68503da9247dfde6585cb8c9fa94897cf21735f8fc1b32116ef474de05c20afa80a9a1bb8b6aad144cfb53e0bab004dd541c8b72025ae694bb60d6050a532208cebb73be883466d18d3b0c06990520e80b936440a2c9fd184d92a1f06c4e8260d00000000000000",
            "04200d6b42350c11df4fcc17987c13d8492ba4e8b3f31eb9baff9be5d8890cfa512d20002df68503da9247dfde6585cb8c9fa94897cf21735f8fc1b32116ef474de05c205991131c5c25911b35fcea2a8343e2dfd7a4d5b45493390e0cb184394d91c349203a3661bc12b72646c94bc6c92796e81953985ee62d80a9ec3645a9a95740ac150e00000000000000",
        ];

        fn assert_root_eq(root: Node, expected: &str) {
            let mut tmp = [0u8; 32];
            root.repr
                .write_le(&mut tmp[..])
                .expect("length is 32 bytes");
            assert_eq!(hex::encode(tmp), expected);
        }

        let mut tree = TestCommitmentTree::new();
        assert_eq!(tree.size(), 0);

        let mut witnesses = vec![];
        let mut paths_i = 0;
        for i in 0..16 {
            let mut cm = FrRepr::default();
            cm.read_le(&hex::decode(commitments[i]).unwrap()[..])
                .expect("length is 32 bytes");

            let cm = Node::new(cm);

            // Witness here
            witnesses.push(TestIncrementalWitness::from_tree(&tree));

            // Now append a commitment to the tree
            assert!(tree.append(cm).is_ok());

            // Size incremented by one.
            assert_eq!(tree.size(), i + 1);

            // Check tree root consistency
            assert_root_eq(tree.root(), roots[i]);

            let mut first = true; // The first witness can never form a path
            for witness in witnesses.as_mut_slice() {
                // Append the same commitment to all the witnesses
                assert!(witness.append(cm).is_ok());

                if first {
                    assert!(witness.path().is_err());
                } else {
                    let path = witness.path().expect("should be able to create a path");
                    let expected = CommitmentTreeWitness::from_slice_with_depth(
                        &mut hex::decode(paths[paths_i]).unwrap(),
                        TESTING_DEPTH,
                    ).unwrap();
                    assert_eq!(path, expected);
                    paths_i += 1;
                }

                first = false;
            }
        }

        // Tree should be full now
        let node = Node::blank();
        assert!(tree.append(node).is_err());
        for witness in witnesses.as_mut_slice() {
            assert!(witness.append(node).is_err());
        }
    }
}