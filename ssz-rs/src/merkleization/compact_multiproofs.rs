//! Experimental support for compact multiproofs.
use crate::{
    lib::*,
    merkleization::{
        multiproofs::{get_helper_indices, get_path_indices},
        GeneralizedIndex, MerkleizationError as Error, Node,
    },
};
use sha2::{Digest, Sha256};

fn compute_proof_indices(indices: &[GeneralizedIndex]) -> Vec<GeneralizedIndex> {
    let mut indices_set: HashSet<GeneralizedIndex> = HashSet::new();
    for &index in indices {
        let helper_indices = get_helper_indices(&[index]);
        for helper_index in helper_indices {
            indices_set.insert(helper_index);
        }
        let path_indices = get_path_indices(index);
        for path_index in path_indices {
            indices_set.remove(&path_index);
        }
        indices_set.insert(index);
    }
    let mut sorted_indices: Vec<GeneralizedIndex> = indices_set.into_iter().collect();
    sorted_indices.sort_by_key(|index| format!("{:b}", *index));
    sorted_indices
}

pub fn compute_proof_descriptor(indices: &[GeneralizedIndex]) -> Result<Vec<u8>, Error> {
    let indices = compute_proof_indices(indices);
    let mut bitstring = String::new();
    for &index in &indices {
        let bin_str = format!("{:b}", index);
        let zeros = bin_str.len() - bin_str.trim_end_matches('0').len();
        bitstring.push_str(&"0".repeat(zeros));
        bitstring.push('1');
    }
    if bitstring.len() % 8 != 0 {
        let additional_bits = 8 - (bitstring.len() % 8);
        bitstring.push_str(&"0".repeat(additional_bits));
    }

    if let Ok(num) = usize::from_str_radix(&bitstring, 2) {
        let bytes = num.to_be_bytes();
        let significant_bytes = (bitstring.len() + 7) / 8;
        Ok(bytes[bytes.len() - significant_bytes..].to_vec())
    } else {
        Err(Error::InvalidDescriptor(bitstring))
    }
}

fn compute_bits_from_proof_descriptor(descriptor: &[u8]) -> Result<Vec<bool>, Error> {
    // Convert bytes to a continuous bit string
    let bitstring: Vec<bool> = descriptor
        .iter()
        .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1 == 1))
        .collect();

    // Find the last '1' in the bitstring
    let last_one_index = bitstring
        .iter()
        .rposition(|&bit| bit)
        .ok_or(Error::InvalidDescriptor("Descriptor does not contain any '1' bits".to_string()))?;

    // Ensure the padding after the last '1' is within the acceptable range
    if bitstring.len() - last_one_index > 8 {
        return Err(Error::InvalidDescriptor(
            "Invalid proof descriptor: padding after the last '1' exceeds 8 bits".to_string(),
        ));
    }

    // Calculate the bit balance and check conditions
    let mut count_0_vs_1 = 0;
    let mut bits = Vec::new();

    for (i, &bit) in bitstring.iter().enumerate().take(last_one_index + 1) {
        bits.push(bit);
        if bit {
            count_0_vs_1 -= 1;
        } else {
            count_0_vs_1 += 1;
        }

        // Check mismatch condition at the last index
        if (count_0_vs_1 < 0) != (i == last_one_index) {
            return Err(Error::InvalidIndexBalanceInDescriptor);
        }
    }

    Ok(bits)
}

struct Pointer {
    bit_index: usize,
    node_index: usize,
}

fn calculate_compact_multi_merkle_root(nodes: &[Node], descriptor: &[u8]) -> Result<Node, Error> {
    let bits = compute_bits_from_proof_descriptor(descriptor)?;
    let mut ptr = Pointer { bit_index: 0, node_index: 0 };
    let root = calculate_compact_multi_merkle_root_inner(nodes, &bits, &mut ptr)?;
    if ptr.bit_index != bits.len() || ptr.node_index != nodes.len() {
        Err(Error::InvalidProof)
    } else {
        Ok(root)
    }
}

fn calculate_compact_multi_merkle_root_inner(
    nodes: &[Node],
    bits: &[bool],
    ptr: &mut Pointer,
) -> Result<Node, Error> {
    let bit = bits[ptr.bit_index];
    ptr.bit_index += 1;
    if bit {
        let node = nodes[ptr.node_index];
        ptr.node_index += 1;
        Ok(node)
    } else {
        let left = calculate_compact_multi_merkle_root_inner(nodes, bits, ptr)?;
        let right = calculate_compact_multi_merkle_root_inner(nodes, bits, ptr)?;
        let mut result = left;
        let mut hasher = Sha256::new();
        hasher.update(left);
        hasher.update(right);
        result.copy_from_slice(&hasher.finalize_reset());
        Ok(result)
    }
}

pub fn verify_compact_merkle_multiproof(
    nodes: &[Node],
    descriptor: &[u8],
    root: Node,
) -> Result<(), Error> {
    if calculate_compact_multi_merkle_root(nodes, descriptor)? == root {
        Ok(())
    } else {
        Err(Error::InvalidProof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merkleization::proofs::tests::decode_node_from_hex;

    #[test]
    fn test_compute_proof_descriptor() {
        assert_eq!(compute_proof_descriptor(&[42]).expect("can make descriptor"), vec![0x25, 0xe0]);
        assert_eq!(
            compute_proof_descriptor(&[5567]).expect("can make descriptor"),
            vec![0x25, 0x2a, 0xaf, 0x80]
        );
        assert_eq!(compute_proof_descriptor(&[66]).expect("can make descriptor"), vec![0x5, 0xf8]);
    }

    #[test]
    fn test_verify_compact_merkle_multiproof() {
        let descriptor = compute_proof_descriptor(&[42]).expect("can make descriptor");

        let expected_state_root = decode_node_from_hex(
            "0x7903bc7cc62f3677c5c0e38562a122638a3627dd945d1f7992e4d32f1d4ef11e",
        );
        let invalid_state_root = decode_node_from_hex(
            "0x7903bc7cc62f3677c5c0e38562a122638a3627dd945d1f7992e4d32f1d4ef11f",
        );

        let branch = [
            "0xa00117d138e95bae66918e6476661d32755f67745f684c90d47f8965327024be",
            "0x822e4005e9a99822945a0fcb648506f3dae4335ca76da7b0cdfe9d4813db0451",
            "0x201d160000000000000000000000000000000000000000000000000000000000",
            "0x572135114f5b6d116e4a6630ba0379c1ea7bacdadc6bd5bf86279ae79279dde1",
            "0x28969b2b8d1a4eead3bbd1815ca49a1efcf9bbb448530b8f1ddac0eb8b96014d",
            "0xcad3a7c4a4edad9f266b0b4052da48011aa7febd52c4b9f3c5293e79c88aa4cf",
        ]
        .into_iter()
        .map(decode_node_from_hex)
        .collect::<Vec<_>>();

        assert!(verify_compact_merkle_multiproof(&branch, &descriptor, expected_state_root).is_ok());
        assert!(verify_compact_merkle_multiproof(&branch, &descriptor, invalid_state_root).is_err());
    }
}
