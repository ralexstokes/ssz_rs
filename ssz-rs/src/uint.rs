use crate::{
    de::{Deserialize, DeserializeError},
    lib::*,
    merkleization::{
        pack_bytes, proofs::Chunkable, GeneralizedIndexable, HashTreeRoot, MerkleizationError,
        Node, BYTES_PER_CHUNK,
    },
    ser::{Serialize, SerializeError},
    visitor::Visitable,
    Serializable, SimpleSerialize, BITS_PER_BYTE,
};

#[inline]
fn bits_to_bytes(count: u32) -> usize {
    (count / BITS_PER_BYTE) as usize
}

macro_rules! define_uint {
    ($uint:ty) => {
        impl Serializable for $uint {
            fn is_variable_size() -> bool {
                false
            }

            fn size_hint() -> usize {
                bits_to_bytes(<$uint>::BITS)
            }
        }

        impl Serialize for $uint {
            fn serialize(&self, buffer: &mut Vec<u8>) -> Result<usize, SerializeError> {
                buffer.extend_from_slice(&self.to_le_bytes());
                Ok(bits_to_bytes(<$uint>::BITS))
            }
        }

        impl Deserialize for $uint {
            fn deserialize(encoding: &[u8]) -> Result<Self, DeserializeError> {
                let byte_size = bits_to_bytes(<$uint>::BITS);
                if encoding.len() < byte_size {
                    return Err(DeserializeError::ExpectedFurtherInput {
                        provided: encoding.len(),
                        expected: byte_size,
                    });
                }
                if encoding.len() > byte_size {
                    return Err(DeserializeError::AdditionalInput {
                        provided: encoding.len(),
                        expected: byte_size,
                    });
                }

                // SAFETY: index is safe because encoding.len() has been checked above; qed
                let bytes = encoding[..byte_size].try_into().expect("slice has right length");
                Ok(<$uint>::from_le_bytes(bytes))
            }
        }

        impl HashTreeRoot for $uint {
            fn hash_tree_root(&self) -> Result<Node, MerkleizationError> {
                let root = self.chunks()?;
                Ok(root.as_slice().try_into().expect("is valid root"))
            }

            fn is_composite_type() -> bool {
                false
            }
        }

        impl GeneralizedIndexable for $uint {
            fn item_length() -> usize {
                Self::size_hint()
            }
        }

        impl Visitable for $uint {}

        impl Chunkable for $uint {
            fn chunks(&self) -> Result<Vec<u8>, MerkleizationError> {
                let mut root = Vec::with_capacity(BYTES_PER_CHUNK);
                let _ = self.serialize(&mut root)?;
                pack_bytes(&mut root);
                Ok(root)
            }
        }

        impl SimpleSerialize for $uint {}
    };
}

define_uint!(u8);
define_uint!(u16);
define_uint!(u32);
define_uint!(u64);
define_uint!(u128);
define_uint!(usize);

/// An unsigned integer represented by 256 bits
pub type U256 = alloy_primitives::U256;

const U256_BYTE_COUNT: usize = 32;

impl Serializable for U256 {
    fn is_variable_size() -> bool {
        false
    }

    fn size_hint() -> usize {
        U256_BYTE_COUNT
    }
}

impl Serialize for U256 {
    fn serialize(&self, buffer: &mut Vec<u8>) -> Result<usize, SerializeError> {
        buffer.extend_from_slice(self.as_le_slice());
        Ok(Self::size_hint())
    }
}

impl Deserialize for U256 {
    fn deserialize(encoding: &[u8]) -> Result<Self, DeserializeError> {
        if encoding.len() < U256_BYTE_COUNT {
            return Err(DeserializeError::ExpectedFurtherInput {
                provided: encoding.len(),
                expected: U256_BYTE_COUNT,
            });
        }
        if encoding.len() > U256_BYTE_COUNT {
            return Err(DeserializeError::AdditionalInput {
                provided: encoding.len(),
                expected: U256_BYTE_COUNT,
            });
        }

        // SAFETY: index is safe because encoding.len() == byte_size; qed
        Ok(Self::from_le_bytes::<U256_BYTE_COUNT>(
            encoding[..U256_BYTE_COUNT].try_into().expect("is correct size"),
        ))
    }
}

impl HashTreeRoot for U256 {
    fn hash_tree_root(&self) -> Result<Node, MerkleizationError> {
        let chunks = self.chunks()?;
        Ok(Node::try_from(chunks.as_slice()).expect("is right size"))
    }

    fn is_composite_type() -> bool {
        false
    }
}

impl GeneralizedIndexable for U256 {
    fn item_length() -> usize {
        Self::size_hint()
    }
}

impl Visitable for U256 {}

impl Chunkable for U256 {
    fn chunks(&self) -> Result<Vec<u8>, MerkleizationError> {
        Ok(self.as_le_bytes().to_vec())
    }
}

impl SimpleSerialize for U256 {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::serialize;

    #[test]
    fn encode_uints() {
        let tests = vec![(u8::default(), [0u8]), (2u8, [2u8]), (u8::MAX, [u8::MAX])];
        for (value, expected) in tests {
            let result = serialize(&value).expect("can encode");
            assert_eq!(result, expected);
        }
        let tests =
            vec![(2u16, [2u8, 0u8]), (1337u16, [57u8, 5u8]), (u16::MAX, [u8::MAX, u8::MAX])];
        for (value, expected) in tests {
            let result = serialize(&value).expect("can encode");
            assert_eq!(result, expected);
        }
        let tests = vec![
            (2u32, [2u8, 0u8, 0u8, 0u8]),
            (1337u32, [57u8, 5u8, 0u8, 0u8]),
            (u32::MAX, [u8::MAX, u8::MAX, u8::MAX, u8::MAX]),
        ];
        for (value, expected) in tests {
            let result = serialize(&value).expect("can encode");
            assert_eq!(result, expected);
        }
        let tests = vec![
            (2u64, [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]),
            (1337u64, [57u8, 5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]),
            (u64::MAX, [u8::MAX; 8]),
        ];
        for (value, expected) in tests {
            let result = serialize(&value).expect("can encode");
            assert_eq!(result, expected);
        }
        let tests = vec![
            (
                2u128,
                [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
            ),
            (
                1337u128,
                [57u8, 5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
            ),
            (u128::MAX, [u8::MAX; 16]),
        ];
        for (value, expected) in tests {
            let result = serialize(&value).expect("can encode");
            assert_eq!(result, expected);
        }
        let tests = vec![
            (U256::try_from_le_slice(&[2u8; 32]).unwrap(), [2u8; 32]),
            (U256::try_from_le_slice(&[u8::MAX; 32]).unwrap(), [u8::MAX; 32]),
        ];
        for (value, expected) in tests {
            let result = serialize(&value).expect("can encode");
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn decode_uints() {
        let tests = vec![(u8::default(), [0u8]), (2u8, [2u8]), (u8::MAX, [u8::MAX])];
        for (expected, bytes) in tests {
            let result = u8::deserialize(&bytes).expect("can encode");
            assert_eq!(result, expected);
        }
        let tests =
            vec![(2u16, [2u8, 0u8]), (1337u16, [57u8, 5u8]), (u16::MAX, [u8::MAX, u8::MAX])];
        for (expected, bytes) in tests {
            let result = u16::deserialize(&bytes).expect("can encode");
            assert_eq!(result, expected);
        }
        let tests = vec![
            (2u32, [2u8, 0u8, 0u8, 0u8]),
            (1337u32, [57u8, 5u8, 0u8, 0u8]),
            (u32::MAX, [u8::MAX, u8::MAX, u8::MAX, u8::MAX]),
        ];
        for (expected, bytes) in tests {
            let result = u32::deserialize(&bytes).expect("can encode");
            assert_eq!(result, expected);
        }
        let tests = vec![
            (2u64, [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]),
            (1337u64, [57u8, 5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]),
            (u64::MAX, [u8::MAX; 8]),
        ];
        for (expected, bytes) in tests {
            let result = u64::deserialize(&bytes).expect("can encode");
            assert_eq!(result, expected);
        }
        let tests = vec![
            (
                2u128,
                [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
            ),
            (
                1337u128,
                [57u8, 5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
            ),
            (u128::MAX, [u8::MAX; 16]),
        ];
        for (expected, bytes) in tests {
            let result = u128::deserialize(&bytes).expect("can encode");
            assert_eq!(result, expected);
        }
        let tests = vec![
            (U256::try_from_le_slice(&[2u8; 32]).unwrap(), [2u8; 32]),
            (U256::try_from_le_slice(&[u8::MAX; 32]).unwrap(), [u8::MAX; 32]),
        ];
        for (expected, bytes) in tests {
            let result = U256::deserialize(&bytes).expect("can encode");
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_serde() {
        let x = U256::from(23);
        let x_str = serde_json::to_string(&x).unwrap();
        let recovered_x = serde_json::from_str(&x_str).unwrap();
        assert_eq!(x, recovered_x);
    }
}
