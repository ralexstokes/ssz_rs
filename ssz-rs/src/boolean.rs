use crate::{
    de::{Deserialize, DeserializeError},
    lib::*,
    merkleization::{
        proofs::Chunkable, GeneralizedIndexable, HashTreeRoot, MerkleizationError, Node,
        BYTES_PER_CHUNK,
    },
    ser::{Serialize, SerializeError},
    visitor::Visitable,
    Serializable, SimpleSerialize,
};

impl Serializable for bool {
    fn is_variable_size() -> bool {
        false
    }

    fn size_hint() -> usize {
        1
    }
}

impl Serialize for bool {
    fn serialize(&self, buffer: &mut Vec<u8>) -> Result<usize, SerializeError> {
        let value = u8::from(*self);
        buffer.push(value);
        Ok(1)
    }
}

impl Deserialize for bool {
    fn deserialize(encoding: &[u8]) -> Result<Self, DeserializeError> {
        match encoding.len() {
            0 => Err(DeserializeError::ExpectedFurtherInput { provided: 0, expected: 1 }),
            // SAFETY: index is safe because encoding is not empty; qed
            1 => match encoding[0] {
                0u8 => Ok(false),
                1u8 => Ok(true),
                b => Err(DeserializeError::InvalidByte(b)),
            },
            n => Err(DeserializeError::AdditionalInput { provided: n, expected: 1 }),
        }
    }
}

impl HashTreeRoot for bool {
    fn hash_tree_root(&self) -> Result<Node, MerkleizationError> {
        let mut node = Node::default();
        if *self {
            node[0] = 1;
        }
        Ok(node)
    }

    fn is_composite_type() -> bool {
        false
    }
}

impl GeneralizedIndexable for bool {
    fn item_length() -> usize {
        Self::size_hint()
    }
}

impl Visitable for bool {}

impl Chunkable for bool {
    fn chunks(&self) -> Result<Vec<u8>, MerkleizationError> {
        let mut vec = vec![0u8; BYTES_PER_CHUNK];
        if *self {
            vec[0] = 1;
        }
        Ok(vec)
    }
}

impl SimpleSerialize for bool {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{deserialize, serialize};

    #[test]
    fn encode_boolean() {
        let tests = vec![(Default::default(), [0u8]), (true, [1u8])];
        for (value, expected) in tests {
            let result = serialize(&value).expect("can encode");
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn decode_boolean() {
        let tests = vec![([0u8], false), ([1u8], true)];
        for (bytes, expected) in tests {
            let result = bool::deserialize(&bytes).expect("can encode");
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn roundtrip_boolean() {
        for value in [true, false].iter() {
            let encoding = serialize(value).expect("can encode");
            let recovered_value: bool = deserialize(&encoding).expect("can decode");
            assert_eq!(*value, recovered_value);
        }
    }
}
