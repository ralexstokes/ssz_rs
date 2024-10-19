//! Experimental support for multiproofs.
use crate::{
    lib::*,
    merkleization::{
        generalized_index::{get_bit, get_path_length, parent, sibling},
        GeneralizedIndex, MerkleizationError as Error, Node,
    },
};
use sha2::{Digest, Sha256};

pub fn get_branch_indices(tree_index: GeneralizedIndex) -> Vec<GeneralizedIndex> {
    let mut focus = sibling(tree_index);
    let mut result = vec![focus];
    while focus > 1 {
        focus = sibling(parent(focus));
        result.push(focus);
    }
    result.truncate(result.len() - 1);
    result
}

pub fn get_path_indices(tree_index: GeneralizedIndex) -> Vec<GeneralizedIndex> {
    let mut focus = tree_index;
    let mut result = vec![focus];
    while focus > 1 {
        focus = parent(focus);
        result.push(focus);
    }
    result.truncate(result.len() - 1);
    result
}

pub fn get_helper_indices(indices: &[GeneralizedIndex]) -> Vec<GeneralizedIndex> {
    let mut all_helper_indices = HashSet::new();
    let mut all_path_indices = HashSet::new();

    for index in indices {
        all_helper_indices.extend(get_branch_indices(*index).iter());
        all_path_indices.extend(get_path_indices(*index).iter());
    }

    let mut all_branch_indices =
        all_helper_indices.difference(&all_path_indices).cloned().collect::<Vec<_>>();
    all_branch_indices.sort_by(|a: &GeneralizedIndex, b: &GeneralizedIndex| b.cmp(a));
    all_branch_indices
}

pub fn calculate_merkle_root(
    leaf: Node,
    proof: &[Node],
    index: GeneralizedIndex,
) -> Result<Node, Error> {
    let path_length = get_path_length(index)?;
    if path_length != proof.len() {
        return Err(Error::InvalidProof);
    }
    let mut result = leaf;

    let mut hasher = Sha256::new();
    for (i, next) in proof.iter().enumerate() {
        if get_bit(index, i) {
            hasher.update(next);
            hasher.update(result);
        } else {
            hasher.update(result);
            hasher.update(next);
        }
        result.copy_from_slice(&hasher.finalize_reset());
    }
    Ok(result)
}

pub fn verify_merkle_proof(
    leaf: Node,
    proof: &[Node],
    index: GeneralizedIndex,
    root: Node,
) -> Result<(), Error> {
    if calculate_merkle_root(leaf, proof, index)? == root {
        Ok(())
    } else {
        Err(Error::InvalidProof)
    }
}

pub fn calculate_multi_merkle_root(
    leaves: &[Node],
    proof: &[Node],
    indices: &[GeneralizedIndex],
) -> Result<Node, Error> {
    if leaves.len() != indices.len() {
        return Err(Error::InvalidProof)
    }
    let helper_indices = get_helper_indices(indices);
    if proof.len() != helper_indices.len() {
        return Err(Error::InvalidProof)
    }

    let mut objects = HashMap::new();
    for (index, node) in indices.iter().zip(leaves.iter()) {
        objects.insert(*index, *node);
    }
    for (index, node) in helper_indices.iter().zip(proof.iter()) {
        objects.insert(*index, *node);
    }

    let mut keys = objects.keys().cloned().collect::<Vec<_>>();
    keys.sort_by(|a, b| b.cmp(a));

    let mut hasher = Sha256::new();
    let mut pos = 0;
    while pos < keys.len() {
        let key = keys.get(pos).unwrap();
        let key_present = objects.contains_key(key);
        let sibling_present = objects.contains_key(&sibling(*key));
        let parent_index = parent(*key);
        let parent_missing = !objects.contains_key(&parent_index);
        let should_compute = key_present && sibling_present && parent_missing;
        if should_compute {
            let right_index = key | 1;
            let left_index = sibling(right_index);
            let left_input = objects.get(&left_index).expect("contains index");
            let right_input = objects.get(&right_index).expect("contains index");
            hasher.update(left_input);
            hasher.update(right_input);

            let parent = objects.entry(parent_index).or_default();
            parent.copy_from_slice(&hasher.finalize_reset());
            keys.push(parent_index);
        }
        pos += 1;
    }

    let root = *objects.get(&1).expect("contains index");
    Ok(root)
}

pub fn verify_merkle_multiproof(
    leaves: &[Node],
    proof: &[Node],
    indices: &[GeneralizedIndex],
    root: Node,
) -> Result<(), Error> {
    if calculate_multi_merkle_root(leaves, proof, indices)? == root {
        Ok(())
    } else {
        Err(Error::InvalidProof)
    }
}
