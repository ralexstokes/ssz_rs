use crate::{lib::*, merkleization::BYTES_PER_CHUNK, prelude::*, visitor::Visitable};

/// Represents a node in a Merkle tree as defined by the SSZ spec.
pub type Node = alloy_primitives::B256;

impl Serialize for Node {
    fn serialize(&self, buffer: &mut Vec<u8>) -> Result<usize, SerializeError> {
        buffer.extend_from_slice(self.as_slice());
        Ok(Self::size_hint())
    }
}

impl Deserialize for Node {
    fn deserialize(encoding: &[u8]) -> Result<Self, DeserializeError> {
        if encoding.len() < BYTES_PER_CHUNK {
            return Err(DeserializeError::ExpectedFurtherInput {
                provided: encoding.len(),
                expected: BYTES_PER_CHUNK,
            });
        }
        if encoding.len() > BYTES_PER_CHUNK {
            return Err(DeserializeError::AdditionalInput {
                provided: encoding.len(),
                expected: BYTES_PER_CHUNK,
            });
        }

        // SAFETY: index is safe because encoding.len() == byte_size; qed
        Ok(Self::from_slice(&encoding[..BYTES_PER_CHUNK]))
    }
}

impl Serializable for Node {
    fn is_variable_size() -> bool {
        false
    }

    fn size_hint() -> usize {
        BYTES_PER_CHUNK
    }
}

impl HashTreeRoot for Node {
    fn hash_tree_root(&self) -> Result<Node, MerkleizationError> {
        let chunks = self.chunks()?;
        Ok(Node::try_from(chunks.as_slice()).expect("is right size"))
    }

    fn is_composite_type() -> bool {
        false
    }
}

impl GeneralizedIndexable for Node {}

impl Visitable for Node {}

impl Chunkable for Node {
    fn chunks(&self) -> Result<Vec<u8>, MerkleizationError> {
        Ok(self.to_vec())
    }
}

impl SimpleSerialize for Node {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde() {
        let mut node = Node::default();
        node[2] = 33;
        let node_repr = serde_json::to_string(&node).unwrap();
        let recovered_node: Node = serde_json::from_str(&node_repr).unwrap();
        assert_eq!(node, recovered_node);
    }

    #[test]
    fn test_fmt() {
        let node = Node::try_from([23u8; 32].as_ref()).unwrap();
        let dbg = format!("{node:?}");
        assert_eq!(dbg, "0x1717171717171717171717171717171717171717171717171717171717171717");
        let display = format!("{node}");
        assert_eq!(display, "0x1717171717171717171717171717171717171717171717171717171717171717");
    }
}
