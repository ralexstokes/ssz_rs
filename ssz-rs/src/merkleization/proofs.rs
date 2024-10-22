//! Support for constructing and verifying Merkle proofs.
pub use crate::merkleization::generalized_index::log_2;
use crate::{
    lib::*,
    merkleization::{
        compute_merkle_tree, GeneralizedIndex, GeneralizedIndexable, MerkleizationError as Error,
        Node, Path,
    },
};
use sha2::{Digest, Sha256};

/// Convenience type for a Merkle proof and the root of the Merkle tree, which serves as
/// "witness" that the proof is valid.
pub type ProofAndWitness = (Proof, Node);

fn get_depth(i: GeneralizedIndex) -> Result<u32, Error> {
    log_2(i).ok_or(Error::InvalidGeneralizedIndex)
}

fn get_index(i: GeneralizedIndex, depth: u32) -> usize {
    i % 2usize.pow(depth)
}

/// Return the index in the layer of the Merkle tree a node with generalized index `index` occupies.
pub fn get_subtree_index(i: GeneralizedIndex) -> Result<usize, Error> {
    let depth = get_depth(i)?;
    Ok(get_index(i, depth))
}

// Identify the generalized index that is the largest parent of `i` that fits in a perfect binary
// tree with `leaf_count` leaves. Return this index along with its depth in the tree
// and its index in the leaf layer.
pub(crate) fn compute_local_merkle_coordinates(
    mut i: GeneralizedIndex,
    leaf_count: usize,
) -> Result<(u32, usize, GeneralizedIndex), Error> {
    let node_count = 2 * leaf_count - 1;
    while i > node_count {
        i /= 2;
    }
    let depth = get_depth(i)?;
    Ok((depth, get_index(i, depth), i))
}

/// A type that knows how to compute Merkle proofs assuming a target type is `Prove`.
#[derive(Debug)]
pub struct Prover {
    hasher: Sha256,
    proof: Proof,
    witness: Node,
}

impl Prover {
    fn set_leaf(&mut self, leaf: &[u8]) {
        self.proof.leaf = leaf.try_into().expect("is correct size");
    }

    // Adds a node to the Merkle proof's branch.
    // Assumes nodes are provided going from the bottom of the tree to the top.
    fn extend_branch(&mut self, node: &[u8]) {
        self.proof.branch.push(node.try_into().expect("is correct size"))
    }

    fn set_witness(&mut self, witness: &[u8]) {
        self.witness = witness.try_into().expect("is correct size");
    }

    /// Derive a Merkle proof relative to `data` given the parameters in `self`.
    pub fn compute_proof<T: Prove + ?Sized>(&mut self, data: &T) -> Result<(), Error> {
        let chunk_count = T::chunk_count();
        let mut leaf_count = chunk_count.next_power_of_two();
        let parent_index = self.proof.index;
        let decoration = data.decoration();
        if decoration.is_some() {
            // double to account for decoration layer
            leaf_count *= 2;
        }

        let (local_depth, local_index, local_generalized_index) =
            compute_local_merkle_coordinates(parent_index, leaf_count)?;

        let mut is_leaf_local = false;
        if local_generalized_index < parent_index {
            // NOTE: need to recurse to children to find ultimate leaf
            let parent_depth = get_depth(parent_index)?;
            let child_depth = parent_depth - local_depth;
            let node_count = 2usize.pow(child_depth);
            let child_index = node_count + parent_index % node_count;
            self.proof.index = child_index;
            data.prove_element(local_index, self)?;
            self.proof.index = parent_index;
        } else {
            // NOTE: leaf is within the current object, set a flag to grab from merkle tree later
            is_leaf_local = true;
        }
        let chunks = data.chunks()?;
        let mut tree = compute_merkle_tree(&mut self.hasher, &chunks, leaf_count)?;
        if let Some(decoration) = decoration {
            tree.mix_in_decoration(decoration, &mut self.hasher)?;
        }

        if is_leaf_local {
            self.set_leaf(&tree[parent_index]);
        }

        let mut target = local_generalized_index;
        for _ in 0..local_depth {
            let sibling = if target % 2 != 0 { &tree[target - 1] } else { &tree[target + 1] };
            self.extend_branch(sibling);
            target /= 2;
        }

        let root = &tree[1];
        self.set_witness(root);

        Ok(())
    }
}

impl From<Prover> for ProofAndWitness {
    fn from(value: Prover) -> Self {
        (value.proof, value.witness)
    }
}

impl From<GeneralizedIndex> for Prover {
    fn from(index: GeneralizedIndex) -> Self {
        Self {
            hasher: Sha256::new(),
            proof: Proof { leaf: Default::default(), branch: vec![], index },
            witness: Default::default(),
        }
    }
}

/// Required functionality to support computing Merkle proofs.
pub trait Prove: GeneralizedIndexable {
    /// Compute the "chunks" of this type as required for the SSZ merkle tree computation.
    /// Default implementation signals an error. Implementing types should override
    /// to provide the correct behavior.
    fn chunks(&self) -> Result<Vec<u8>, Error> {
        Err(Error::NotChunkable)
    }

    /// Construct a proof of the member element located at the type-specific `index` assuming the
    /// context in `prover`.
    #[allow(unused)]
    fn prove_element(&self, index: usize, prover: &mut Prover) -> Result<(), Error> {
        Err(Error::NoInnerElement)
    }

    /// Returns the "decoration" if this type has any in the Merkle tree.
    /// For `List`s, the length of the list is hashed into the root of the Merkle tree.
    /// For unions, the type of the currently occupied variant is hashed into the root of the Merkle
    /// tree.
    fn decoration(&self) -> Option<usize> {
        None
    }

    /// Compute a Merkle proof of `Self` at the type's `path`, along with the root of the Merkle
    /// tree as a witness value.
    fn prove(&self, path: Path) -> Result<ProofAndWitness, Error> {
        let index = Self::generalized_index(path)?;
        let mut prover = Prover::from(index);
        prover.compute_proof(self)?;
        Ok(prover.into())
    }
}

/// Contains data necessary to verify `leaf` was included under some witness "root" node
/// at the generalized position `index`.
#[derive(Debug, PartialEq, Eq)]
pub struct Proof {
    pub leaf: Node,
    pub branch: Vec<Node>,
    pub index: GeneralizedIndex,
}

impl Proof {
    /// Verify `self` against the provided `root` witness node.
    /// This `root` is the hash tree root of the SSZ object that produced the proof.
    /// See `Prover` for further information.
    pub fn verify(&self, root: Node) -> Result<(), Error> {
        is_valid_merkle_branch_for_generalized_index(self.leaf, &self.branch, self.index, root)
    }
}

/// Verifies the Merkle proof against the `root` given the other metadata, assuming `leaf` occupies
/// the `generalized_index` in the tree.
pub fn is_valid_merkle_branch_for_generalized_index(
    leaf: Node,
    branch: &[Node],
    generalized_index: GeneralizedIndex,
    root: Node,
) -> Result<(), Error> {
    let depth = log_2(generalized_index).ok_or(Error::InvalidGeneralizedIndex)? as usize;
    let index = get_subtree_index(generalized_index)?;
    is_valid_merkle_branch(leaf, branch, depth, index, root)
}

/// `is_valid_merkle_branch` verifies the Merkle proof against the `root` given the other metadata.
pub fn is_valid_merkle_branch(
    leaf: Node,
    branch: &[Node],
    depth: usize,
    index: usize,
    root: Node,
) -> Result<(), Error> {
    if branch.len() != depth {
        return Err(Error::InvalidProof)
    }

    let mut derived_root = leaf;
    let mut hasher = Sha256::new();

    for (i, node) in branch.iter().enumerate() {
        if (index / 2usize.pow(i as u32)) % 2 != 0 {
            hasher.update(node);
            hasher.update(derived_root);
        } else {
            hasher.update(derived_root);
            hasher.update(node);
        }
        derived_root.copy_from_slice(&hasher.finalize_reset());
    }

    if derived_root == root {
        Ok(())
    } else {
        Err(Error::InvalidProof)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::prelude::*;
    use alloy_primitives::hex::FromHex;

    pub(crate) fn decode_node_from_hex(hex: &str) -> Node {
        Node::from_hex(hex).unwrap()
    }

    pub(crate) fn compute_and_verify_proof_for_path<T: SimpleSerialize>(data: &T, path: Path) {
        let (proof, witness) = data.prove(path).unwrap();
        assert_eq!(witness, data.hash_tree_root().unwrap());
        let result = proof.verify(witness);
        if let Err(err) = result {
            panic!("{err} for {proof:?} with witness {witness}")
        }
    }

    #[test]
    fn test_is_valid_merkle_branch() {
        let leaf = decode_node_from_hex(
            "94159da973dfa9e40ed02535ee57023ba2d06bad1017e451055470967eb71cd5",
        );
        let branch = [
            "8f594dbb4f4219ad4967f86b9cccdb26e37e44995a291582a431eef36ecba45c",
            "f8c2ed25e9c31399d4149dcaa48c51f394043a6a1297e65780a5979e3d7bb77c",
            "382ba9638ce263e802593b387538faefbaed106e9f51ce793d405f161b105ee6",
        ]
        .into_iter()
        .map(decode_node_from_hex)
        .collect::<Vec<_>>();
        let depth = 3;
        let index = 2;
        let root = decode_node_from_hex(
            "27097c728aade54ff1376d5954681f6d45c282a81596ef19183148441b754abb",
        );

        assert!(is_valid_merkle_branch(leaf, &branch, depth, index, root).is_ok());
    }

    #[test]
    fn test_simple_proof() {
        let leaf = decode_node_from_hex(
            "94159da973dfa9e40ed02535ee57023ba2d06bad1017e451055470967eb71cd5",
        );
        let branch = [
            "8f594dbb4f4219ad4967f86b9cccdb26e37e44995a291582a431eef36ecba45c",
            "f8c2ed25e9c31399d4149dcaa48c51f394043a6a1297e65780a5979e3d7bb77c",
            "382ba9638ce263e802593b387538faefbaed106e9f51ce793d405f161b105ee6",
        ]
        .into_iter()
        .map(decode_node_from_hex)
        .collect::<Vec<_>>();
        let depth = 3;
        let index = 2;
        let proof = Proof { leaf, branch, index: 2usize.pow(depth) + index };
        let root = decode_node_from_hex(
            "27097c728aade54ff1376d5954681f6d45c282a81596ef19183148441b754abb",
        );
        let result = proof.verify(root);
        assert!(result.is_ok());
    }

    #[test]
    fn test_proving_primitives_fails_with_bad_path() {
        let data = 8u8;
        let result = data.prove(&[PathElement::Length]);
        assert!(result.is_err());

        let data = true;
        let result = data.prove(&[234.into()]);
        assert!(result.is_err());
    }

    #[test]
    fn test_prove_primitives() {
        let data = 8u8;
        compute_and_verify_proof_for_path(&data, &[]);

        let data = 0u8;
        compute_and_verify_proof_for_path(&data, &[]);

        let data = 234238u64;
        compute_and_verify_proof_for_path(&data, &[]);

        let data = 0u128;
        compute_and_verify_proof_for_path(&data, &[]);

        let data = u128::MAX;
        compute_and_verify_proof_for_path(&data, &[]);

        let data = U256::from_str_radix(
            "f8c2ed25e9c31399d4149dcaa48c51f394043a6a1297e65780a5979e3d7bb77c",
            16,
        )
        .unwrap();
        compute_and_verify_proof_for_path(&data, &[]);

        let data = true;
        compute_and_verify_proof_for_path(&data, &[]);

        let data = false;
        compute_and_verify_proof_for_path(&data, &[]);
    }
}
