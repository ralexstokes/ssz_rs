use crate::{
    de::{Deserialize, DeserializeError},
    lib::*,
    merkleization::{
        mix_in_selector, proofs::Chunkable, GeneralizedIndex, GeneralizedIndexable, HashTreeRoot,
        MerkleizationError, Node, Path, PathElement, BYTES_PER_CHUNK,
    },
    ser::{Serialize, SerializeError},
    visitor::{self, Visitable, Visitor},
    Serializable, SimpleSerialize,
};

/// `SimpleSerialize` is implemented for `Option` as a convenience
/// when the schema is equivalent to one described by:
/// enum Option<T: SimpleSerialize> {
///     None,
///     Some(T),
/// }
/// The SSZ schema for this value would be `Union[None, T]`.
impl<T: Serializable> Serializable for Option<T> {
    fn is_variable_size() -> bool {
        true
    }

    fn size_hint() -> usize {
        0
    }
}

impl<T> Serialize for Option<T>
where
    T: Serializable,
{
    fn serialize(&self, buffer: &mut Vec<u8>) -> Result<usize, SerializeError> {
        match self {
            Some(data) => {
                let selector_bytes = 1u8.serialize(buffer)?;
                let value_bytes = data.serialize(buffer)?;
                Ok(selector_bytes + value_bytes)
            }
            None => 0u8.serialize(buffer),
        }
    }
}

impl<T> Deserialize for Option<T>
where
    T: Serializable,
{
    fn deserialize(encoding: &[u8]) -> Result<Self, DeserializeError> {
        if encoding.is_empty() {
            return Err(DeserializeError::ExpectedFurtherInput { provided: 0, expected: 1 });
        }

        // SAFETY: index is safe because encoding is not empty; qed
        match encoding[0] {
            0 => {
                if encoding.len() != 1 {
                    return Err(DeserializeError::AdditionalInput {
                        provided: encoding.len(),
                        expected: 1,
                    });
                }
                Ok(None)
            }
            1 => {
                // SAFETY: index is safe because encoding is not empty; qed
                let inner = T::deserialize(&encoding[1..])?;
                Ok(Some(inner))
            }
            b => Err(DeserializeError::InvalidByte(b)),
        }
    }
}

impl<T> HashTreeRoot for Option<T>
where
    T: SimpleSerialize,
{
    fn hash_tree_root(&self) -> Result<Node, MerkleizationError> {
        let chunks = Node::try_from(self.chunks()?.as_slice()).expect("is correct size");
        match self {
            Some(_) => Ok(mix_in_selector(chunks, 1)),
            None => Ok(mix_in_selector(chunks, 0)),
        }
    }
}

impl<T> GeneralizedIndexable for Option<T>
where
    T: SimpleSerialize,
{
    fn compute_generalized_index(
        parent: GeneralizedIndex,
        path: Path,
    ) -> Result<GeneralizedIndex, MerkleizationError> {
        if let Some((next, rest)) = path.split_first() {
            match next {
                PathElement::Index(i) => {
                    if *i >= 2 {
                        return Err(MerkleizationError::InvalidPathElement(next.clone()));
                    }
                    let child = parent * 2;
                    match i {
                        0 => {
                            if rest.is_empty() {
                                Ok(child)
                            } else {
                                Err(MerkleizationError::InvalidPath(rest.to_vec()))
                            }
                        }
                        1 => T::compute_generalized_index(child, rest),
                        _ => unreachable!("validated in covered range"),
                    }
                }
                PathElement::Selector => {
                    if rest.is_empty() {
                        Ok(parent * 2 + 1)
                    } else {
                        Err(MerkleizationError::InvalidPath(rest.to_vec()))
                    }
                }
                elem => Err(MerkleizationError::InvalidPathElement(elem.clone())),
            }
        } else {
            Ok(parent)
        }
    }
}

impl<T> Visitable for Option<T>
where
    T: SimpleSerialize + Visitable,
{
    fn visit_element<V: Visitor>(&self, index: usize, visitor: &mut V) -> Result<(), V::Error> {
        if index >= 2 {
            Err(visitor::VisitorError::InvalidInnerIndex.into())
        } else {
            match self {
                Some(value) => visitor.visit(value),
                None => {
                    let leaf = 0usize;
                    visitor.visit(&leaf)
                }
            }
        }
    }

    fn element_count(&self) -> usize {
        2
    }
}

impl<T> Chunkable for Option<T>
where
    T: SimpleSerialize,
{
    fn chunks(&self) -> Result<Vec<u8>, MerkleizationError> {
        match self {
            Some(value) => {
                let root = value.hash_tree_root()?;
                Ok(root.to_vec())
            }
            None => Ok(vec![0u8; BYTES_PER_CHUNK]),
        }
    }

    fn decoration(&self) -> Option<usize> {
        match self {
            Some(_) => Some(1),
            None => Some(0),
        }
    }
}

impl<T> SimpleSerialize for Option<T> where T: SimpleSerialize {}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[derive(Debug, PartialEq, Eq, SimpleSerialize)]
    enum AnotherOption {
        None,
        A(u8),
        B(u8),
    }

    impl Default for AnotherOption {
        fn default() -> Self {
            Self::None
        }
    }

    #[derive(Debug, Default, PartialEq, Eq, SimpleSerialize)]
    struct Inner {
        data: List<u8, 8>,
    }

    #[derive(Debug, PartialEq, Eq, SimpleSerialize)]
    enum Foo {
        A(u32),
        B(u8),
    }

    impl Default for Foo {
        fn default() -> Self {
            Self::A(Default::default())
        }
    }

    #[derive(Debug, PartialEq, Eq, SimpleSerialize)]
    enum Bar {
        A(u32),
        B(Vector<u8, 4>),
    }

    impl Default for Bar {
        fn default() -> Self {
            Self::A(Default::default())
        }
    }

    #[derive(Debug, PartialEq, Eq, SimpleSerialize)]
    enum Baz {
        A(u32),
        B(Inner),
        C(List<u8, 12>),
    }

    impl Default for Baz {
        fn default() -> Self {
            Self::A(Default::default())
        }
    }

    #[derive(Debug, PartialEq, Eq, SimpleSerialize)]
    enum Boo {
        A(u32),
        B(Inner),
        C(List<u8, 12>),
        D(Vector<u8, 2>),
    }

    impl Default for Boo {
        fn default() -> Self {
            Self::A(Default::default())
        }
    }

    #[test]
    fn test_option() {
        let mut x = Some(12u8);
        let mut buffer = vec![];
        let result = x.serialize(&mut buffer).expect("can encode");
        assert_eq!(result, 2);
        let expected = [1u8, 12u8];
        assert_eq!(buffer, expected);

        x = None;
        let mut buffer = vec![];
        let result = x.serialize(&mut buffer).expect("can encode");
        assert_eq!(result, 1);
        let expected = [0u8];
        assert_eq!(buffer, expected);

        x = Some(34u8);
        let mut buffer = vec![];
        let _ = x.serialize(&mut buffer).expect("can serialize");
        let recovered = Option::<u8>::deserialize(&buffer).expect("can decode");
        assert_eq!(x, recovered);
    }

    #[test]
    fn test_options_with_extra_input() {
        let buffer = vec![0u8, 123, 234];
        let result = Option::<u8>::deserialize(&buffer);
        assert!(matches!(result, Err(DeserializeError::AdditionalInput { .. })));

        let buffer = vec![0u8, 123, 234];
        let result = AnotherOption::deserialize(&buffer);
        assert!(matches!(result, Err(DeserializeError::AdditionalInput { .. })));
    }

    #[test]
    fn test_another_option() {
        let mut x = AnotherOption::A(12u8);
        let mut buffer = vec![];
        let result = x.serialize(&mut buffer).expect("can encode");
        assert_eq!(result, 2);
        let expected = [1u8, 12u8];
        assert_eq!(buffer, expected);

        x = AnotherOption::None;
        let mut buffer = vec![];
        let result = x.serialize(&mut buffer).expect("can encode");
        assert_eq!(result, 1);
        let expected = [0u8];
        assert_eq!(buffer, expected);

        x = AnotherOption::B(32u8);
        let mut buffer = vec![];
        let _ = x.serialize(&mut buffer).expect("can serialize");
        let recovered = AnotherOption::deserialize(&buffer).expect("can decode");
        assert_eq!(x, recovered);
    }

    #[test]
    fn encode_union() {
        let value = Foo::A(12u32);

        let mut buffer = vec![];
        let result = value.serialize(&mut buffer).expect("can serialize");
        assert_eq!(result, 5);
        let expected = [0u8, 12u8, 0u8, 0u8, 0u8];
        assert_eq!(buffer, expected);

        let value = Foo::B(6u8);

        let mut buffer = vec![];
        let result = value.serialize(&mut buffer).expect("can serialize");
        assert_eq!(result, 2);
        let expected = [1u8, 6u8];
        assert_eq!(buffer, expected);

        let value = Bar::A(12u32);

        let mut buffer = vec![];
        let result = value.serialize(&mut buffer).expect("can serialize");
        assert_eq!(result, 5);
        let expected = [0u8, 12u8, 0u8, 0u8, 0u8];
        assert_eq!(buffer, expected);

        let value = Bar::B(Vector::try_from(vec![3u8, 2u8, 1u8, 10u8]).unwrap());

        let mut buffer = vec![];
        let result = value.serialize(&mut buffer).expect("can serialize");
        assert_eq!(result, 5);
        let expected = [1u8, 3u8, 2u8, 1u8, 10u8];
        assert_eq!(buffer, expected);

        let value = Baz::A(12u32);

        let mut buffer = vec![];
        let result = value.serialize(&mut buffer).expect("can serialize");
        assert_eq!(result, 5);
        let expected = [0u8, 12u8, 0u8, 0u8, 0u8];
        assert_eq!(buffer, expected);

        let value = Baz::B(Inner { data: List::try_from(vec![123u8]).unwrap() });

        let mut buffer = vec![];
        let result = value.serialize(&mut buffer).expect("can serialize");
        assert_eq!(result, 6);
        let expected = [1u8, 4u8, 0u8, 0u8, 0u8, 123u8];
        assert_eq!(buffer, expected);

        let value = Baz::C(List::try_from(vec![123u8, 253u8]).unwrap());

        let mut buffer = vec![];
        let result = value.serialize(&mut buffer).expect("can serialize");
        assert_eq!(result, 3);
        let expected = [2u8, 123u8, 253u8];
        assert_eq!(buffer, expected);

        let value = Boo::A(12u32);

        let mut buffer = vec![];
        let result = value.serialize(&mut buffer).expect("can serialize");
        assert_eq!(result, 5);
        let expected = [0u8, 12u8, 0u8, 0u8, 0u8];
        assert_eq!(buffer, expected);

        let value = Boo::B(Inner { data: List::try_from(vec![123u8]).unwrap() });

        let mut buffer = vec![];
        let result = value.serialize(&mut buffer).expect("can serialize");
        assert_eq!(result, 6);
        let expected = [1u8, 4u8, 0u8, 0u8, 0u8, 123u8];
        assert_eq!(buffer, expected);

        let value = Boo::C(List::try_from(vec![123u8, 253u8]).unwrap());

        let mut buffer = vec![];
        let result = value.serialize(&mut buffer).expect("can serialize");
        assert_eq!(result, 3);
        let expected = [2u8, 123u8, 253u8];
        assert_eq!(buffer, expected);

        let value = Boo::D(Vector::try_from(vec![123u8, 253u8]).unwrap());

        let mut buffer = vec![];
        let result = value.serialize(&mut buffer).expect("can serialize");
        assert_eq!(result, 3);
        let expected = [3u8, 123u8, 253u8];
        assert_eq!(buffer, expected);
    }

    #[test]
    fn decode_union() {
        let data = [0u8, 12u8, 0u8, 0u8, 0u8];
        let result = Boo::deserialize(&data).expect("can decode");
        let value = Boo::A(12u32);
        assert_eq!(result, value);

        let data = [1u8, 4u8, 0u8, 0u8, 0u8, 123u8];
        let result = Boo::deserialize(&data).expect("can decode");
        let value = Boo::B(Inner { data: List::try_from(vec![123u8]).unwrap() });
        assert_eq!(result, value);

        let data = [2u8, 123u8, 253u8];
        let result = Boo::deserialize(&data).expect("can decode");
        let value = Boo::C(List::try_from(vec![123u8, 253u8]).unwrap());
        assert_eq!(result, value);

        let data = [3u8, 123u8, 253u8];
        let result = Boo::deserialize(&data).expect("can decode");
        let value = Boo::D(Vector::try_from(vec![123u8, 253u8]).unwrap());
        assert_eq!(result, value);
    }

    #[test]
    fn roundtrip_union() {
        let value = Boo::default();
        let mut buffer = vec![];
        let _ = value.serialize(&mut buffer).expect("can serialize");
        let recovered = Boo::deserialize(&buffer).expect("can decode");
        assert_eq!(value, recovered);
        assert_eq!(value, Boo::A(u32::default()));

        let value = Boo::B(Inner { data: List::try_from(vec![123u8]).unwrap() });
        let mut buffer = vec![];
        let _ = value.serialize(&mut buffer).expect("can serialize");
        let recovered = Boo::deserialize(&buffer).expect("can decode");
        assert_eq!(value, recovered);

        let value = Boo::C(List::try_from(vec![123u8, 253u8]).unwrap());
        let mut buffer = vec![];
        let _ = value.serialize(&mut buffer).expect("can serialize");
        let recovered = Boo::deserialize(&buffer).expect("can decode");
        assert_eq!(value, recovered);

        let value = Boo::D(Vector::try_from(vec![123u8, 253u8]).unwrap());
        let mut buffer = vec![];
        let _ = value.serialize(&mut buffer).expect("can serialize");
        let recovered = Boo::deserialize(&buffer).expect("can decode");
        assert_eq!(value, recovered);
    }

    #[test]
    fn prove_option() {
        let data = Some(11u8);
        let path = &[0.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let data = Some(11u8);
        let path = &[1.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let data = Some(U256::from(23423u16));
        let path = &[0.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let data = Some(U256::from(23423u16));
        let path = &[1.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let path = &[PathElement::Selector];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let data = Option::<U256>::None;
        let path = &[0.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let data = Option::<U256>::None;
        let path = &[1.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let data = Option::<u16>::None;
        let path = &[0.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let data = Option::<u16>::None;
        let path = &[1.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let path = &[PathElement::Selector];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);
    }

    #[test]
    fn prove_unions() {
        let data = Boo::default();
        let path = &[0.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let data = Boo::B(Default::default());
        let path = &[1.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);
        let path = &[1.into(), "data".into(), 7.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let data = Boo::C(Default::default());
        let path = &[2.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);
        let path = &[2.into(), 0.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let data = Boo::D(Default::default());
        let path = &[3.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);

        let path = &[3.into(), 0.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);
        let path = &[3.into(), 1.into()];
        crate::merkleization::proofs::tests::compute_and_verify_proof_for_path(&data, path);
    }
}
