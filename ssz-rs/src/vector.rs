use crate::{
    de::{deserialize_homogeneous_composite, Deserialize, DeserializeError},
    error::{Error, InstanceError, TypeError},
    lib::*,
    merkleization::{
        elements_to_chunks, get_power_of_two_ceil, merkleize, pack, proofs::Chunkable,
        GeneralizedIndex, GeneralizedIndexable, HashTreeRoot, MerkleizationError, Node, Path,
        PathElement,
    },
    ser::{Serialize, SerializeError, Serializer},
    visitor::{self, Visitable, Visitor},
    Serializable, SimpleSerialize,
};

/// A homogenous collection of a fixed number of values.
///
/// NOTE: a `Vector` of length `0` is illegal.
#[derive(PartialOrd, Ord, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize), serde(transparent))]
pub struct Vector<T: Serializable, const N: usize> {
    data: Vec<T>,
}

impl<T: Serializable, const N: usize> AsRef<[T]> for Vector<T, N> {
    fn as_ref(&self) -> &[T] {
        &self.data
    }
}

impl<T: Serializable + PartialEq, const N: usize> PartialEq for Vector<T, N> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T: Serializable + Eq, const N: usize> Eq for Vector<T, N> {}

impl<T: Serializable, const N: usize> TryFrom<Vec<T>> for Vector<T, N> {
    type Error = (Vec<T>, Error);

    fn try_from(data: Vec<T>) -> Result<Self, Self::Error> {
        if N == 0 {
            return Err((data, Error::Type(TypeError::InvalidBound(N))));
        }
        if data.len() != N {
            let len = data.len();
            Err((data, Error::Instance(InstanceError::Exact { required: N, provided: len })))
        } else {
            Ok(Self { data })
        }
    }
}

impl<T, const N: usize> TryFrom<&[T]> for Vector<T, N>
where
    T: Serializable + Clone,
{
    type Error = Error;

    fn try_from(data: &[T]) -> Result<Self, Self::Error> {
        if N == 0 {
            return Err(Error::Type(TypeError::InvalidBound(N)));
        }
        if data.len() != N {
            let len = data.len();
            Err(Error::Instance(InstanceError::Exact { required: N, provided: len }))
        } else {
            Ok(Self { data: data.to_vec() })
        }
    }
}

impl<T, const N: usize> fmt::Debug for Vector<T, N>
where
    T: Serializable + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if f.alternate() {
            write!(f, "Vector<{}, {}>{:#?}", any::type_name::<T>(), N, self.data)
        } else {
            write!(f, "Vector<{}, {}>{:?}", any::type_name::<T>(), N, self.data)
        }
    }
}

impl<T, const N: usize> Default for Vector<T, N>
where
    T: Serializable + Default,
{
    fn default() -> Self {
        // SAFETY: there is currently no way to enforce statically
        // that `N` is non-zero with const generics so panics are possible.
        assert!(N > 0);

        let mut data = Vec::with_capacity(N);
        for _ in 0..N {
            data.push(T::default());
        }

        // SAFETY: panic can't happen because data.len() == N != 0; qed
        data.try_into()
            // need to drop data so we do not require it as Debug as required by `expect`
            .map_err(|(_, err)| err)
            .expect("any Vector can be constructed with nonzero default data")
    }
}

impl<T, const N: usize> Deref for Vector<T, N>
where
    T: Serializable,
{
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T, const N: usize> DerefMut for Vector<T, N>
where
    T: Serializable,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl<T, Idx: SliceIndex<[T]>, const N: usize> Index<Idx> for Vector<T, N>
where
    T: Serializable,
{
    type Output = <Idx as SliceIndex<[T]>>::Output;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.data[index]
    }
}

impl<T, Idx: SliceIndex<[T]>, const N: usize> IndexMut<Idx> for Vector<T, N>
where
    T: Serializable,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.data[index]
    }
}

impl<T, const N: usize> Serializable for Vector<T, N>
where
    T: Serializable,
{
    fn is_variable_size() -> bool {
        T::is_variable_size()
    }

    fn size_hint() -> usize {
        T::size_hint() * N
    }
}

impl<T, const N: usize> Serialize for Vector<T, N>
where
    T: Serializable,
{
    fn serialize(&self, buffer: &mut Vec<u8>) -> Result<usize, SerializeError> {
        if N == 0 {
            return Err(TypeError::InvalidBound(N).into());
        }
        let mut serializer = Serializer::default();
        for element in &self.data {
            serializer.with_element(element)?;
        }
        serializer.serialize(buffer)
    }
}

impl<T, const N: usize> Deserialize for Vector<T, N>
where
    T: Serializable,
{
    fn deserialize(encoding: &[u8]) -> Result<Self, DeserializeError> {
        if N == 0 {
            return Err(TypeError::InvalidBound(N).into());
        }
        if !T::is_variable_size() {
            let expected_length = N * T::size_hint();
            if encoding.len() < expected_length {
                return Err(DeserializeError::ExpectedFurtherInput {
                    provided: encoding.len(),
                    expected: expected_length,
                });
            }
            if encoding.len() > expected_length {
                return Err(DeserializeError::AdditionalInput {
                    provided: encoding.len(),
                    expected: expected_length,
                });
            }
        }
        let inner = deserialize_homogeneous_composite(encoding)?;
        inner.try_into().map_err(|(_, err)| match err {
            Error::Deserialize(err) => err,
            Error::Instance(err) => DeserializeError::InvalidInstance(err),
            Error::Type(err) => DeserializeError::InvalidType(err),
            _ => unreachable!("no other error variant can be returned at this point"),
        })
    }
}

impl<T, const N: usize> Vector<T, N>
where
    T: SimpleSerialize,
{
    fn assemble_chunks(&self) -> Result<Vec<u8>, MerkleizationError> {
        if T::is_composite_type() {
            let count = self.len();
            elements_to_chunks(self.data.iter().enumerate(), count)
        } else {
            pack(&self.data)
        }
    }

    fn compute_hash_tree_root(&self) -> Result<Node, MerkleizationError> {
        let chunks = self.assemble_chunks()?;
        merkleize(&chunks, None)
    }
}

impl<T, const N: usize> HashTreeRoot for Vector<T, N>
where
    T: SimpleSerialize,
{
    fn hash_tree_root(&self) -> Result<Node, MerkleizationError> {
        self.compute_hash_tree_root()
    }
}

impl<T, const N: usize> GeneralizedIndexable for Vector<T, N>
where
    T: SimpleSerialize,
{
    fn chunk_count() -> usize {
        (N * T::item_length() + 31) / 32
    }

    fn compute_generalized_index(
        parent: GeneralizedIndex,
        path: Path,
    ) -> Result<GeneralizedIndex, MerkleizationError> {
        if let Some((next, rest)) = path.split_first() {
            match next {
                PathElement::Index(i) => {
                    if *i >= N {
                        return Err(MerkleizationError::InvalidPathElement(next.clone()));
                    }
                    let chunk_position = i * T::item_length() / 32;
                    let child =
                        parent * get_power_of_two_ceil(Self::chunk_count()) + chunk_position;
                    T::compute_generalized_index(child, rest)
                }
                elem => Err(MerkleizationError::InvalidPathElement(elem.clone())),
            }
        } else {
            Ok(parent)
        }
    }
}

impl<T, const N: usize> Visitable for Vector<T, N>
where
    T: SimpleSerialize + Visitable,
{
    fn visit_element<V: Visitor>(&self, index: usize, visitor: &mut V) -> Result<(), V::Error> {
        if index >= N {
            Err(visitor::VisitorError::InvalidInnerIndex.into())
        } else {
            let child = &self[index];
            visitor.visit(child)
        }
    }

    fn element_count(&self) -> usize {
        N
    }
}

impl<T, const N: usize> Chunkable for Vector<T, N>
where
    T: SimpleSerialize,
{
    fn chunks(&self) -> Result<Vec<u8>, MerkleizationError> {
        self.assemble_chunks()
    }
}

impl<T, const N: usize> SimpleSerialize for Vector<T, N> where T: SimpleSerialize {}

#[cfg(feature = "serde")]
struct VectorVisitor<T: Serializable>(PhantomData<Vec<T>>);

#[cfg(feature = "serde")]
impl<'de, T: Serializable + serde::Deserialize<'de>> serde::de::Visitor<'de> for VectorVisitor<T> {
    type Value = Vec<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("sequence")
    }

    fn visit_seq<S>(self, visitor: S) -> Result<Self::Value, S::Error>
    where
        S: serde::de::SeqAccess<'de>,
    {
        serde::Deserialize::deserialize(serde::de::value::SeqAccessDeserializer::new(visitor))
    }
}

#[cfg(feature = "serde")]
impl<'de, T: Serializable + serde::Deserialize<'de>, const N: usize> serde::Deserialize<'de>
    for Vector<T, N>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let data = deserializer.deserialize_seq(VectorVisitor(PhantomData))?;
        Vector::<T, N>::try_from(data).map_err(|(_, err)| serde::de::Error::custom(err))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        lib::cmp::Ordering,
        list::List,
        proofs::{Prove, Prover},
        serialize, U256,
    };

    const COUNT: usize = 32;

    #[test]
    fn test_try_from() {
        let mut data = vec![2u8; 10];
        data.extend_from_slice(&[0u8; 10]);

        let vector = Vector::<u8, 20>::try_from(data).unwrap();
        assert_eq!(vector[..10], [2u8; 10]);
        assert_eq!(vector[10..], [0u8; 10]);
    }

    #[test]
    #[should_panic]
    fn test_try_from_invalid() {
        let data = vec![2u8; 10];
        let vector = Vector::<u8, 1>::try_from(data).unwrap();
        assert_eq!(vector[0], 2u8);
    }

    #[test]
    fn encode_vector() {
        let data = vec![33u16; COUNT];
        let mut value = Vector::<u16, COUNT>::try_from(data).unwrap();

        value[0] = 34u16;
        assert_eq!(value[0], 34u16);
        value[0] = 33u16;
        let encoding = serialize(&value).expect("can encode");
        let expected = [
            33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8,
            33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8,
            33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8,
            33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8, 33u8, 0u8,
        ];
        assert_eq!(encoding, expected);
    }

    #[test]
    fn decode_vector() {
        let bytes = vec![
            0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 0u8,
            1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8,
        ];
        let result = Vector::<u8, COUNT>::deserialize(&bytes).expect("can deserialize");
        let expected: Vector<u8, COUNT> = bytes.try_into().expect("test data");
        assert_eq!(result, expected);
    }

    #[test]
    fn decode_vector_with_no_input() {
        let source = vec![];
        let result = Vector::<u8, 6>::deserialize(&source);
        assert!(matches!(result, Err(DeserializeError::ExpectedFurtherInput { .. })));
    }

    #[test]
    fn decode_variable_vector() {
        const COUNT: usize = 4;
        let mut inner: Vec<List<u8, 1>> =
            Vec::from_iter((0..4).map(|i| List::try_from(vec![i]).unwrap()));
        let permutation = &mut inner[3];
        let _ = permutation.pop().expect("test data correct");
        let input: Vector<List<u8, 1>, COUNT> = inner.try_into().expect("test data correct");
        let mut buffer = vec![];
        let _ = input.serialize(&mut buffer).expect("can serialize");
        let expected = vec![16, 0, 0, 0, 17, 0, 0, 0, 18, 0, 0, 0, 19, 0, 0, 0, 0, 1, 2];
        assert_eq!(buffer, expected);
    }

    #[test]
    fn roundtrip_vector() {
        let bytes = vec![
            0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 0u8,
            1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8,
        ];
        let input: Vector<u8, COUNT> = bytes.try_into().expect("test data");
        let mut buffer = vec![];
        let _ = input.serialize(&mut buffer).expect("can serialize");
        let recovered = Vector::<u8, COUNT>::deserialize(&buffer).expect("can decode");
        assert_eq!(input, recovered);
    }

    #[test]
    fn roundtrip_variable_vector() {
        const COUNT: usize = 4;
        let mut inner: Vec<List<u8, 1>> =
            Vec::from_iter((0..4).map(|i| List::try_from(vec![i]).unwrap()));
        let permutation = &mut inner[3];
        let _ = permutation.pop().expect("test data correct");
        let input: Vector<List<u8, 1>, COUNT> = inner.try_into().expect("test data correct");
        let mut buffer = vec![];
        let _ = input.serialize(&mut buffer).expect("can serialize");
        let recovered = Vector::<List<u8, 1>, COUNT>::deserialize(&buffer).expect("can decode");
        assert_eq!(input, recovered);
    }

    #[test]
    fn can_iter_vector() {
        let bytes = vec![
            0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 0u8,
            1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8,
        ];
        let mut input: Vector<u8, COUNT> = bytes.try_into().expect("test data");
        for (i, &value) in input.iter().enumerate() {
            assert_eq!(value as usize, i % 8);
        }
        for value in input.iter_mut() {
            *value = 1;
            assert_eq!(*value, 1);
        }
    }

    #[test]
    fn test_serde() {
        type V = Vector<u8, 4>;
        let data = vec![1u8, 0, 22, 33];
        let input = V::try_from(data).unwrap();
        let input_str = serde_json::to_string(&input).unwrap();
        let recovered_input: V = serde_json::from_str(&input_str).unwrap();
        assert_eq!(input, recovered_input);
    }

    #[test]
    #[should_panic]
    fn test_illegal_serde() {
        type V = Vector<u8, 4>;
        let bad_input_str = "[]";
        let _: V = serde_json::from_str(bad_input_str).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_illegal_generalized_index() {
        type V = Vector<u8, 4>;

        let path = &[5.into()];
        let _ = V::generalized_index(path).unwrap();
    }

    #[test]
    fn test_generalized_index_for_vector_over_non_aligned_vector() {
        type W = Vector<u64, 2>;
        type V = Vector<W, 2>;

        let path = &[0.into(), 0.into()];
        let index = V::generalized_index(path).unwrap();
        assert_eq!(index, 2);

        let path = &[0.into(), 1.into()];
        let index = V::generalized_index(path).unwrap();
        assert_eq!(index, 2);

        let path = &[1.into(), 0.into()];
        let index = V::generalized_index(path).unwrap();
        assert_eq!(index, 3);

        let path = &[1.into(), 1.into()];
        let index = V::generalized_index(path).unwrap();
        assert_eq!(index, 3);
    }

    #[test]
    fn test_generalized_index_for_vector_over_aligned_vector() {
        type W = Vector<U256, 2>;
        type V = Vector<W, 2>;

        let path = &[0.into(), 0.into()];
        let index = V::generalized_index(path).unwrap();
        assert_eq!(index, 4);

        let path = &[0.into(), 1.into()];
        let index = V::generalized_index(path).unwrap();
        assert_eq!(index, 5);

        let path = &[1.into(), 0.into()];
        let index = V::generalized_index(path).unwrap();
        assert_eq!(index, 6);

        let path = &[1.into(), 1.into()];
        let index = V::generalized_index(path).unwrap();
        assert_eq!(index, 7);
    }

    fn compute_and_verify_proof_against_index<T: SimpleSerialize>(
        data: &T,
        path: Path,
        expected_index: GeneralizedIndex,
    ) {
        let (proof, witness) = data.prove(path).unwrap();
        assert!(proof.verify(witness).is_ok());

        let index = T::generalized_index(path).unwrap();
        assert_eq!(expected_index, index);
        let mut prover = Prover::from(expected_index);
        prover.compute_proof(data).unwrap();
        let (proof_from_index, witness_from_index) = prover.into();
        assert_eq!(proof, proof_from_index);
        assert_eq!(witness, witness_from_index);
        assert!(proof.verify(witness).is_ok());
    }

    #[test]
    fn test_prove_vector_over_aligned_primitive() {
        type V = Vector<U256, 7>;

        let data = V::try_from(vec![
            U256::from(23),
            U256::from(34),
            U256::from(45),
            U256::from(56),
            U256::from(67),
            U256::from(78),
            U256::from(11),
        ])
        .unwrap();

        let path = &[3.into()];
        let expected_index = 11;
        compute_and_verify_proof_against_index(&data, path, expected_index);
    }

    #[test]
    fn test_prove_vector_over_non_aligned_primitive() {
        type V = Vector<u64, 7>;

        let data = V::try_from(vec![23, 34, 45, 56, 67, 78, 11]).unwrap();

        let path = &[3.into()];
        let expected_index = 2;
        compute_and_verify_proof_against_index(&data, path, expected_index);
    }

    #[test]
    fn test_prove_vector_over_vector_of_non_aligned_primitives() {
        type W = Vector<bool, 2>;
        type V = Vector<W, 2>;

        let inner = W::try_from(vec![true, true]).unwrap();
        let data = V::try_from(vec![inner.clone(), inner]).unwrap();

        // prove into non-leaf
        let path = &[0.into()];
        let expected_index = 2;
        compute_and_verify_proof_against_index(&data, path, expected_index);

        let path = &[1.into()];
        let expected_index = 3;
        compute_and_verify_proof_against_index(&data, path, expected_index);

        // prove into leaf
        let path = &[0.into(), 0.into()];
        let expected_index = 2;
        compute_and_verify_proof_against_index(&data, path, expected_index);

        let path = &[0.into(), 1.into()];
        let expected_index = 2;
        compute_and_verify_proof_against_index(&data, path, expected_index);

        let path = &[1.into(), 0.into()];
        let expected_index = 3;
        compute_and_verify_proof_against_index(&data, path, expected_index);

        let path = &[1.into(), 1.into()];
        let expected_index = 3;
        compute_and_verify_proof_against_index(&data, path, expected_index);
    }

    #[test]
    fn test_prove_vector_over_vector_of_aligned_primitives() {
        type W = Vector<U256, 2>;
        type V = Vector<W, 2>;

        let inner = W::try_from(vec![U256::from(1), U256::from(2)]).unwrap();
        let data = V::try_from(vec![inner.clone(), inner]).unwrap();

        // prove into non-leaf
        let path = &[0.into()];
        let expected_index = 2;
        compute_and_verify_proof_against_index(&data, path, expected_index);

        let path = &[1.into()];
        let expected_index = 3;
        compute_and_verify_proof_against_index(&data, path, expected_index);

        // prove into leaf
        let path = &[0.into(), 0.into()];
        let expected_index = 4;
        compute_and_verify_proof_against_index(&data, path, expected_index);

        let path = &[0.into(), 1.into()];
        let expected_index = 5;
        compute_and_verify_proof_against_index(&data, path, expected_index);

        let path = &[1.into(), 0.into()];
        let expected_index = 6;
        compute_and_verify_proof_against_index(&data, path, expected_index);

        let path = &[1.into(), 1.into()];
        let expected_index = 7;
        compute_and_verify_proof_against_index(&data, path, expected_index);
    }

    #[test]
    fn test_prove_vector_with_smaller_wrapper_and_aligned_member() {
        type T = U256;
        const W_BOUND: usize = 18;
        type W = Vector<T, W_BOUND>;
        const V_BOUND: usize = 2;
        type V = Vector<W, V_BOUND>;

        let inner = W::try_from(vec![T::from(11u32); W_BOUND]).unwrap();
        let data = V::try_from(vec![inner; V_BOUND]).unwrap();

        for i in 0..V_BOUND {
            for j in 0..W_BOUND {
                let path = &[i.into(), j.into()];
                crate::proofs::tests::compute_and_verify_proof_for_path(&data, path);
            }
        }
    }

    #[test]
    fn test_prove_vector_with_smaller_wrapper_and_non_aligned_member() {
        type T = u64;
        const W_BOUND: usize = 18;
        type W = Vector<T, W_BOUND>;
        const V_BOUND: usize = 2;
        type V = Vector<W, V_BOUND>;

        let inner = W::try_from(vec![T::from(11u32); W_BOUND]).unwrap();
        let data = V::try_from(vec![inner; V_BOUND]).unwrap();

        for i in 0..V_BOUND {
            for j in 0..W_BOUND {
                let path = &[i.into(), j.into()];
                crate::proofs::tests::compute_and_verify_proof_for_path(&data, path);
            }
        }
    }

    #[test]
    fn test_prove_vector_with_larger_wrapper_and_aligned_member() {
        type T = U256;
        const W_BOUND: usize = 3;
        type W = Vector<T, W_BOUND>;
        const V_BOUND: usize = 18;
        type V = Vector<W, V_BOUND>;

        let inner = W::try_from(vec![T::from(11u32); W_BOUND]).unwrap();
        let data = V::try_from(vec![inner; V_BOUND]).unwrap();

        for i in 0..V_BOUND {
            for j in 0..W_BOUND {
                let path = &[i.into(), j.into()];
                crate::proofs::tests::compute_and_verify_proof_for_path(&data, path);
            }
        }
    }

    #[test]
    fn test_prove_vector_with_larger_wrapper_and_non_aligned_member() {
        type T = u64;
        const W_BOUND: usize = 3;
        type W = Vector<T, W_BOUND>;
        const V_BOUND: usize = 18;
        type V = Vector<W, V_BOUND>;

        let inner = W::try_from(vec![T::from(11u32); W_BOUND]).unwrap();
        let data = V::try_from(vec![inner; V_BOUND]).unwrap();

        for i in 0..V_BOUND {
            for j in 0..W_BOUND {
                let path = &[i.into(), j.into()];
                crate::proofs::tests::compute_and_verify_proof_for_path(&data, path);
            }
        }
    }

    #[test]
    fn test_ord() {
        type V = Vector<U256, 7>;

        let data = V::try_from(vec![
            U256::from(23),
            U256::from(34),
            U256::from(45),
            U256::from(56),
            U256::from(67),
            U256::from(78),
            U256::from(11),
        ])
        .unwrap();

        let other = V::try_from(vec![
            U256::from(23),
            U256::from(34),
            U256::from(45),
            U256::from(56),
            U256::from(67),
            U256::from(78),
            U256::from(11),
        ])
        .unwrap();

        assert_eq!(data.cmp(&other), Ordering::Equal);

        let another = V::try_from(vec![
            U256::from(23),
            U256::from(34),
            U256::from(45),
            U256::from(56),
            U256::from(67),
            U256::from(78),
            U256::from(12),
        ])
        .unwrap();

        assert_eq!(data.cmp(&another), Ordering::Less);
    }
}
