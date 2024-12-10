//! Experimental support for multiproofs.
use crate::{
    lib::*,
    merkleization::{
        generalized_index::{get_bit, get_path_length, parent, sibling},
        GeneralizedIndex, MerkleizationError as Error, Node,
    },
};
use sha2::{Digest, Sha256};

fn get_branch_indices(tree_index: GeneralizedIndex) -> Vec<GeneralizedIndex> {
    let mut focus = sibling(tree_index);
    let mut result = vec![focus];
    while focus > 1 {
        focus = sibling(parent(focus));
        result.push(focus);
    }
    result.truncate(result.len() - 1);
    result
}

fn get_path_indices(tree_index: GeneralizedIndex) -> Vec<GeneralizedIndex> {
    let mut focus = tree_index;
    let mut result = vec![focus];
    while focus > 1 {
        focus = parent(focus);
        result.push(focus);
    }
    result.truncate(result.len() - 1);
    result
}

// Returns the indices of the nodes that are needed to compute the root of a multiproof.
pub fn get_helper_indices(indices: &[GeneralizedIndex]) -> Vec<GeneralizedIndex> {
    let mut all_helper_indices = HashSet::new();
    let mut all_path_indices = HashSet::new();

    // Collect all indices that are needed to compute the root.
    for index in indices {
        all_helper_indices.extend(get_branch_indices(*index).iter());
        all_path_indices.extend(get_path_indices(*index).iter());
    }

    // Remove the indices that are already in the path.
    let mut all_branch_indices =
        all_helper_indices.difference(&all_path_indices).cloned().collect::<Vec<_>>();

    // Sort the indices in descending order.
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
    // Validate input
    if leaves.len() != indices.len() {
        return Err(Error::InvalidProof);
    }
    // Get all indices that are needed to compute the root.
    // aka those that aren't on the direct path from the leaves to the root.
    let helper_indices = get_helper_indices(indices);
    if proof.len() != helper_indices.len() {
        return Err(Error::InvalidProof);
    }

    // Create map of known nodes
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
        // Check if the key is present
        let key_present = objects.contains_key(key);
        // Check if the sibling is present
        let sibling_present = objects.contains_key(&sibling(*key));
        let parent_index = parent(*key);
        // Check if the parent is missing
        let parent_missing = !objects.contains_key(&parent_index);
        // If the key and sibling is present and parent is missing, compute the parent
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_merkle_multiproof() {
        //        Root
        //        /  \
        //    Leaf1  ProofNode
        //   (idx2)  (idx3)
        let leaf1 = {
            let mut node = Node::default();
            node[0] = 1;
            node
        };

        // Single proof node
        let proof_node = {
            let mut node = Node::default();
            node[0] = 2;
            node
        };

        // Just try to verify a single leaf
        let leaves = vec![leaf1];
        let indices = vec![2];
        let proof = vec![proof_node];

        // Calculate root we expect
        let mut hasher = Sha256::new();
        hasher.update(leaf1.as_slice());
        hasher.update(proof_node.as_slice());
        let mut root = Node::default();
        root.copy_from_slice(&hasher.finalize());

        let result = verify_merkle_multiproof(&leaves, &proof, &indices, root);
        assert!(result.is_ok());
    }

    #[test]
    fn test_verify_merkle_multiproof_multiple() {
        // Constructing a deeper Merkle tree:
        //                  Root (1)
        //                /          \
        //          Node2 (2)        Node3 (3)
        //          /     \            /     \
        //     Node4 (4)  Node5(5)  Node6 (6)  Node7 (7)
        //      / \        / \        / \        / \
        //    L8   L9    L10  L11   L12  L13   L14  L15

        // Create leaf nodes
        let leaves = (8..=15).map(create_node).collect::<Vec<_>>();
        let leaf_map: HashMap<GeneralizedIndex, Node> =
            (8..=15).map(|i| (i, leaves[(i - 8) as usize])).collect();

        // Hash intermediate nodes
        let node4 = hash_nodes(&leaf_map[&8], &leaf_map[&9]);
        let node5 = hash_nodes(&leaf_map[&10], &leaf_map[&11]);
        let node6 = hash_nodes(&leaf_map[&12], &leaf_map[&13]);
        let node7 = hash_nodes(&leaf_map[&14], &leaf_map[&15]);
        let node2 = hash_nodes(&node4, &node5);
        let node3 = hash_nodes(&node6, &node7);

        // Compute the root
        let root = hash_nodes(&node2, &node3);

        // Define the leaves to prove and their indices
        let proof_leaves = vec![leaf_map[&8], leaf_map[&13]];
        let proof_indices = vec![8, 13];

        // Define the proof nodes
        // [12, 9, 7, 5]
        let proof_nodes = vec![
            leaf_map[&12], // Sibling of Leaf13
            leaf_map[&9],  // Sibling of Leaf8
            node7.clone(), // Sibling of Node6
            node5.clone(), // Sibling of Node4
        ];

        // Perform the multiproof verification
        let result = verify_merkle_multiproof(&proof_leaves, &proof_nodes, &proof_indices, root);

        assert!(
            result.is_ok(),
            "Multiproof verification failed for multiple leaves in a deeper tree"
        );
    }

    // Helper function to create a node with a specific value
    fn create_node(value: u8) -> Node {
        let mut node = Node::default();
        node[0] = value;
        node
    }

    // Helper function to hash two child nodes to create a parent node
    fn hash_nodes(left: &Node, right: &Node) -> Node {
        let mut hasher = Sha256::new();
        hasher.update(left);
        hasher.update(right);
        let mut parent = Node::default();
        parent.copy_from_slice(&hasher.finalize());
        parent
    }
}
