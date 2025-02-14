//! Provides a set of macros to derive implementations for the core SSZ traits given in the `ssz_rs`
//! crate. Suppports native Rust structs and enums, subject to conditions compatible with SSZ
//! containers and unions.
//!
//! Refer to the `examples` in the `ssz_rs` crate for a better idea on how to use this derive macro.
//!
//! This proc macro supports one attribute `ssz(transparent)` to pass through calls on a wrapping
//! Rust enum to the underlying data. Refers to this crate's tests for example usage.
use proc_macro2::TokenStream;
use quote::{format_ident, quote, quote_spanned};
use syn::{
    parse_macro_input, spanned::Spanned, Attribute, Data, DeriveInput, Field, Fields, Generics,
    Ident, Meta, NestedMeta, PathArguments,
};

// NOTE: copied here from `ssz_rs` crate as it is unlikely to change
// and can keep it out of the crate's public interface.
const BYTES_PER_CHUNK: usize = 32;

const SSZ_HELPER_ATTRIBUTE: &str = "ssz";

fn derive_serialize_impl(data: &Data, helper_attr: Option<&HelperAttr>) -> TokenStream {
    match data {
        Data::Struct(ref data) => {
            let fields = match data.fields {
                // "regular" struct with 1+ fields
                Fields::Named(ref fields) => &fields.named,
                // "tuple" struct
                // only support the case with one unnamed field, to support "newtype" pattern
                Fields::Unnamed(..) => {
                    return quote! {
                        fn serialize(&self, buffer: &mut Vec<u8>) -> Result<usize, ssz_rs::SerializeError> {
                                self.0.serialize(buffer)
                        }
                    }
                }
                _ => unimplemented!(
                    "this type of struct is currently not supported by this derive macro"
                ),
            };
            let serialization_by_field = fields.iter().map(|f| match &f.ident {
                Some(field_name) => quote_spanned! { f.span() =>
                    serializer.with_element(&self.#field_name)?;
                },
                None => panic!("should have already returned an impl"),
            });

            quote! {
                fn serialize(&self, buffer: &mut Vec<u8>) -> Result<usize, ssz_rs::SerializeError> {
                    let mut serializer = ssz_rs::__internal::Serializer::default();

                    #(#serialization_by_field)*

                    serializer.serialize(buffer)
                }
            }
        }
        Data::Enum(ref data) => {
            let serialization_by_variant = data.variants.iter().enumerate().map(|(i, variant)| {
                let variant_name = &variant.ident;
                match &variant.fields {
                    Fields::Unnamed(..) => {
                        if matches!(helper_attr, Some(&HelperAttr::Transparent)) {
                            quote_spanned! { variant.span() =>
                                Self::#variant_name(value) => value.serialize(buffer),
                            }
                        } else {
                            quote_spanned! { variant.span() =>
                                Self::#variant_name(value) => {
                                    let selector = #i as u8;
                                    let selector_bytes = selector.serialize(buffer)?;
                                    let value_bytes  = value.serialize(buffer)?;
                                    Ok(selector_bytes + value_bytes)
                                }
                            }
                        }
                    }
                    Fields::Unit => {
                        quote_spanned! { variant.span() =>
                            Self::None => {
                                0u8.serialize(buffer)
                            }
                        }
                    }
                    _ => unreachable!(),
                }
            });

            quote! {
                fn serialize(&self, buffer: &mut Vec<u8>) -> Result<usize, ssz_rs::SerializeError> {
                    match self {
                        #(#serialization_by_variant)*
                    }
                }
            }
        }
        Data::Union(..) => unreachable!("data was already validated to exclude union types"),
    }
}

fn derive_deserialize_impl(data: &Data, helper_attr: Option<&HelperAttr>) -> TokenStream {
    match data {
        Data::Struct(ref data) => {
            let fields = match data.fields {
                // "regular" struct with 1+ fields
                Fields::Named(ref fields) => &fields.named,
                // "tuple" struct
                // only support the case with one unnamed field, to support "newtype" pattern
                Fields::Unnamed(ref fields) => {
                    // SAFETY: index is safe because Punctuated always has a first element; qed
                    let f = &fields.unnamed[0];
                    let field_type = &f.ty;
                    return quote! {
                        fn deserialize(encoding: &[u8]) -> Result<Self, ssz_rs::DeserializeError> {
                            let result = <#field_type>::deserialize(&encoding)?;
                            Ok(Self(result))
                        }
                    };
                }
                _ => unimplemented!(
                    "this type of struct is currently not supported by this derive macro"
                ),
            };
            let deserialization_by_field = fields.iter().map(|f| {
                let field_type = &f.ty;
                match &f.ident {
                    Some(_) => quote_spanned! { f.span() =>
                        deserializer.parse::<#field_type>(encoding)?;
                    },
                    None => panic!("should have already returned an impl"),
                }
            });

            let initialization_by_field = fields.iter().enumerate().map(|(i, f)| {
                let field_type = &f.ty;
                match &f.ident {
                    Some(field_name) => quote_spanned! { f.span() =>
                        #field_name: <#field_type>::deserialize(&encoding[spans[2*#i]..spans[2*#i+1]])?,
                    },
                    None => panic!("should have already returned an impl"),
                }
            });

            quote! {
                fn deserialize(encoding: &[u8]) -> Result<Self, ssz_rs::DeserializeError> {
                    let mut deserializer = ssz_rs::__internal::ContainerDeserializer::default();

                    #(#deserialization_by_field)*

                    let spans = deserializer.finalize(encoding)?;

                    Ok(Self {
                        #(#initialization_by_field)*
                    })
                }
            }
        }
        Data::Enum(ref data) => {
            let body = if matches!(helper_attr, Some(&HelperAttr::Transparent)) {
                let deserialization_by_variant = data.variants.iter().rev().map(|variant| {
                    // NOTE: this is "safe" as the number of legal variants fits into `u8`
                    let variant_name = &variant.ident;
                    match &variant.fields {
                        Fields::Unnamed(inner) => {
                            // SAFETY: index is safe because Punctuated always has a first
                            // element; qed
                            let variant_type = &inner.unnamed[0];
                            quote_spanned! { variant.span() =>
                                if let Ok(value) = <#variant_type>::deserialize(encoding) {
                                    return Ok(Self::#variant_name(value))
                                }
                            }
                        }
                        _ => unreachable!("validated to exclude this condition"),
                    }
                });
                quote! {
                    #(#deserialization_by_variant)*
                    Err(ssz_rs::DeserializeError::NoMatchingVariant)
                }
            } else {
                let deserialization_by_variant =
                    data.variants.iter().enumerate().map(|(i, variant)| {
                        // NOTE: this is "safe" as the number of legal variants fits into `u8`
                        let i = i as u8;
                        let variant_name = &variant.ident;
                        match &variant.fields {
                            Fields::Unnamed(inner) => {
                                // SAFETY: index is safe because Punctuated always has a first
                                // element; qed
                                let variant_type = &inner.unnamed[0];
                                quote_spanned! { variant.span() =>
                                    #i => {
                                        // SAFETY: index is safe because encoding isn't empty; qed
                                        let value = <#variant_type>::deserialize(&encoding[1..])?;
                                        Ok(Self::#variant_name(value))
                                    }
                                }
                            }
                            Fields::Unit => {
                                quote_spanned! { variant.span() =>
                                    0 => {
                                        if encoding.len() != 1 {
                                            return Err(DeserializeError::AdditionalInput {
                                                provided: encoding.len(),
                                                expected: 1,
                                            })
                                        }
                                        Ok(Self::None)
                                    },
                                }
                            }
                            _ => unreachable!(),
                        }
                    });
                quote! {
                    // SAFETY: index is safe because encoding isn't empty; qed
                    match encoding[0] {
                        #(#deserialization_by_variant)*
                        b => Err(ssz_rs::DeserializeError::InvalidByte(b)),
                    }
                }
            };

            quote! {
                fn deserialize(encoding: &[u8]) -> Result<Self, ssz_rs::DeserializeError> {
                    if encoding.is_empty() {
                        return Err(ssz_rs::DeserializeError::ExpectedFurtherInput {
                            provided: 0,
                            expected: 1,
                        });
                    }

                    #body
                }
            }
        }
        Data::Union(..) => unreachable!("data was already validated to exclude union types"),
    }
}

fn derive_variable_size_impl(data: &Data) -> TokenStream {
    match data {
        Data::Struct(ref data) => {
            let fields = match data.fields {
                Fields::Named(ref fields) => &fields.named,
                Fields::Unnamed(ref fields) => &fields.unnamed,
                _ => unimplemented!(
                    "this type of struct is currently not supported by this derive macro"
                ),
            };
            let impl_by_field = fields.iter().map(|f| {
                let field_type = &f.ty;
                quote_spanned! { f.span() =>
                    <#field_type>::is_variable_size()
                }
            });

            quote! {
                #(#impl_by_field)|| *
            }
        }
        Data::Enum(..) => {
            // NOTE: interaction with `transparent` attribute:
            // no code in this repo should ever directly call this generated method
            // on the "wrapping enum" used with `transparent`
            // thus, we can simply provide the existing implementation
            quote! { true }
        }
        Data::Union(..) => unreachable!("data was already validated to exclude union types"),
    }
}

fn derive_size_hint_impl(data: &Data) -> TokenStream {
    match data {
        Data::Struct(ref data) => {
            let fields = match data.fields {
                Fields::Named(ref fields) => &fields.named,
                Fields::Unnamed(ref fields) => &fields.unnamed,
                _ => unimplemented!(
                    "this type of struct is currently not supported by this derive macro"
                ),
            };
            let impl_by_field = fields.iter().map(|f| {
                let field_type = &f.ty;
                quote_spanned! { f.span() =>
                    <#field_type>::size_hint()
                }
            });

            quote! {
                if Self::is_variable_size() {
                    0
                } else {
                    #(#impl_by_field)+ *
                }
            }
        }
        Data::Enum(..) => {
            // NOTE: interaction with `transparent` attribute:
            // no code in this repo should ever directly call this generated method
            // on the "wrapping enum" used with `transparent`
            // thus, we can simply provide the existing implementation
            quote! { 0 }
        }
        Data::Union(..) => unreachable!("data was already validated to exclude union types"),
    }
}

fn derive_merkleization_impl(
    data: &Data,
    name: &Ident,
    generics: &Generics,
    helper_attr: Option<&HelperAttr>,
) -> TokenStream {
    let (hash_tree_root_impl, chunks_impl) = match data {
        Data::Struct(ref data) => {
            let fields = match data.fields {
                Fields::Named(ref fields) => &fields.named,
                Fields::Unnamed(ref fields) => &fields.unnamed,
                _ => unimplemented!(
                    "this type of struct is currently not supported by this derive macro"
                ),
            };
            let field_count = fields.iter().len();
            let impl_by_field = fields.iter().enumerate().map(|(i, f)| match &f.ident {
                Some(field_name) => quote_spanned! { f.span() =>
                    let chunk = self.#field_name.hash_tree_root()?;
                    let range = #i*#BYTES_PER_CHUNK..(#i+1)*#BYTES_PER_CHUNK;
                    chunks[range].copy_from_slice(chunk.as_ref());
                },
                None => quote_spanned! { f.span() =>
                    let chunk = self.0.hash_tree_root()?;
                    let range = #i*#BYTES_PER_CHUNK..(#i+1)*#BYTES_PER_CHUNK;
                    chunks[range].copy_from_slice(chunk.as_ref());
                },
            });
            let chunks_impl = quote! {
                let mut chunks = vec![0u8; #field_count * #BYTES_PER_CHUNK];
                #(#impl_by_field)*
                Ok(chunks)
            };
            let hash_tree_root_impl = quote! {
                let chunks = self.assemble_chunks()?;
                ssz_rs::__internal::merkleize(&chunks, None)
            };
            (hash_tree_root_impl, chunks_impl)
        }
        Data::Enum(ref data) => {
            let implementations = data.variants.iter().enumerate().map(|(i, variant)| {
                let variant_name = &variant.ident;
                match &variant.fields {
                    Fields::Unnamed(..) => {
                        // NOTE: validated to only be `transparent` operation at this point...
                        let hash_tree_by_variant = if helper_attr.is_some() {
                            quote_spanned! { variant.span() =>
                               Self::#variant_name(value) => value.hash_tree_root(),
                            }
                        } else {
                            quote_spanned! { variant.span() =>
                               Self::#variant_name(value) => {
                                   let selector = #i;
                                   let chunks = value.hash_tree_root()?;
                                   Ok(ssz_rs::__internal::mix_in_selector(chunks, selector))
                               }
                            }
                        };
                        let chunks_by_variant = quote! {
                           Self::#variant_name(value) => Ok(value.hash_tree_root()?.to_vec()),
                        };
                        (hash_tree_by_variant, chunks_by_variant)
                    }
                    Fields::Unit => (
                        quote_spanned! { variant.span() =>
                            Self::None => Ok(ssz_rs::__internal::mix_in_selector(
                                Node::default(),
                                0,
                            )),
                        },
                        quote! {
                            Self::None => Ok(Node::default().to_vec()),
                        },
                    ),
                    _ => unreachable!(),
                }
            });
            let (hash_tree_root_by_variant, chunks_by_variant): (Vec<_>, Vec<_>) =
                implementations.unzip();
            (
                quote! {
                    match self {
                        #(#hash_tree_root_by_variant)*
                    }
                },
                quote! {
                    match self {
                        #(#chunks_by_variant)*
                    }
                },
            )
        }
        Data::Union(..) => unreachable!("data was already validated to exclude union types"),
    };
    let (impl_generics, ty_generics, _) = generics.split_for_impl();
    quote! {
        impl #impl_generics #name #ty_generics {
            fn assemble_chunks(&self) -> Result<Vec<u8>, ssz_rs::MerkleizationError> {
                #chunks_impl
            }
        }

        impl #impl_generics ssz_rs::HashTreeRoot for #name #ty_generics {
            fn hash_tree_root(&self) -> Result<ssz_rs::Node, ssz_rs::MerkleizationError> {
                #hash_tree_root_impl
            }
        }
    }
}

fn derive_generalized_indexable_impl(
    data: &Data,
    name: &Ident,
    generics: &Generics,
) -> TokenStream {
    let (impl_generics, ty_generics, _) = generics.split_for_impl();

    let (compute_generalized_index_impl, helper_impl) = match data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let trait_impl = quote! {
                    if let Some((next, rest)) = path.split_first() {
                        match next {
                            PathElement::Field(field) => {
                                Self::__ssz_rs_generalized_index_by_field(parent, rest, field)
                            }
                            elem => Err(MerkleizationError::InvalidPathElement(elem.clone())),
                        }
                    } else {
                        Ok(parent)
                    }
                };
                let fields = &fields.named;
                let impl_by_field = fields.iter().enumerate().map(|(i, field)| {
                    let field_name = field.ident.as_ref().expect("only named fields");
                    let selector = format!("{field_name}");
                    let field_ty = &field.ty;
                    quote! {
                        #selector => {
                            let chunk_position = #i;
                            let child = parent * ssz_rs::__internal::get_power_of_two_ceil(Self::chunk_count()) + chunk_position;
                            <#field_ty as ssz_rs::GeneralizedIndexable>::compute_generalized_index(child, path)
                        }
                    }
                });
                let helper_impl = quote! {
                    impl #impl_generics #name #ty_generics {
                        fn __ssz_rs_generalized_index_by_field(
                            parent: ssz_rs::GeneralizedIndex,
                            path: ssz_rs::Path,
                            field: &str,
                        ) -> Result<ssz_rs::GeneralizedIndex, ssz_rs::MerkleizationError> {
                            match field {
                                #(#impl_by_field)*
                                s => Err(MerkleizationError::InvalidPathElement(PathElement::Field(s.to_string()))),
                            }
                        }
                    }
                };
                (trait_impl, Some(helper_impl))
            }
            Fields::Unnamed(ref fields) => {
                let field = fields.unnamed.first().expect("validated to only have one field");
                let ty = &field.ty;
                let trait_impl = quote! {
                    <#ty as ssz_rs::GeneralizedIndexable>::compute_generalized_index(parent, path)
                };
                (trait_impl, None)
            }
            Fields::Unit => unreachable!("validated to exclude this type"),
        },
        Data::Enum(ref data) => {
            let variant_count = data.variants.len();

            let impl_by_variant = data.variants.iter().enumerate().map(|(i, variant)| {
                let variant_name = &variant.ident;
                match &variant.fields {
                    Fields::Unnamed(ref fields) => {
                        let field =
                            fields.unnamed.first().expect("validated to only have one field");
                        let ty = &field.ty;
                        quote! {
                            #i => {
                                <#ty as ssz_rs::GeneralizedIndexable>::compute_generalized_index(child, rest)
                            }
                        }
                    }
                    Fields::Unit => {
                        // NOTE: this has already been validated to conform to:
                        // first variant, and is `None` identifier
                        if i != 0 || !is_valid_none_identifier(variant_name) {
                            panic!("internal validation inconsistency; check proc derive macro");
                        }
                        quote! {
                            0 => {
                                if rest.is_empty() {
                                    Ok(child)
                                } else {
                                    Err(MerkleizationError::InvalidPath(rest.to_vec()))
                                }
                            }
                        }
                    }
                    _ => unreachable!(),
                }
            });

            let trait_impl = quote! {
                if let Some((next, rest)) = path.split_first() {
                    match next {
                        PathElement::Index(i) => {
                            if *i >= #variant_count {
                                return Err(MerkleizationError::InvalidPathElement(next.clone()))
                            }
                            let child = parent * 2;
                            match *i {
                                #(#impl_by_variant)*
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
            };
            (trait_impl, None)
        }
        Data::Union(..) => unreachable!("data was already validated to exclude union types"),
    };

    let chunk_count_impl = match data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let fields = &fields.named;
                let field_count = fields.iter().len();
                quote! {
                    fn chunk_count() -> usize {
                        #field_count
                    }
                }
            }
            Fields::Unnamed(ref fields) => {
                // NOTE: "newtype" pattern
                let field = fields.unnamed.first().expect("validated to only have one field");
                let ty = &field.ty;
                quote! {
                    fn chunk_count() -> usize {
                        <#ty as ssz_rs::GeneralizedIndexable>::chunk_count()
                    }
                }
            }
            Fields::Unit => unreachable!("validated to exclude this type"),
        },
        Data::Enum(_) => quote!(), // use trait default impl
        Data::Union(..) => unreachable!("data was already validated to exclude union types"),
    };

    quote! {
        #helper_impl

        impl #impl_generics ssz_rs::GeneralizedIndexable for #name #ty_generics {
            #chunk_count_impl

            fn compute_generalized_index(
                parent: ssz_rs::GeneralizedIndex,
                path: ssz_rs::Path,
            ) -> Result<ssz_rs::GeneralizedIndex, ssz_rs::MerkleizationError> {
                #compute_generalized_index_impl
            }
        }
    }
}

fn derive_chunkable_impl(data: &Data, name: &Ident, generics: &Generics) -> TokenStream {
    let (impl_generics, ty_generics, _) = generics.split_for_impl();

    let (chunks_impl, decoration_impl) = match data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref _fields) => {
                let chunks_impl = quote! {
                    self.assemble_chunks()
                };
                (chunks_impl, None)
            }
            Fields::Unnamed(..) => {
                // NOTE: new type pattern, proxy to wrapped type...
                let chunks_impl = quote! {
                    self.0.chunks()
                };

                let decoration_impl = quote! {
                    fn decoration(&self) -> Option<usize> {
                        self.0.decoration()
                    }
                };
                (chunks_impl, Some(decoration_impl))
            }
            Fields::Unit => unreachable!("validated to exclude this type"),
        },
        Data::Enum(ref data) => {
            let decoration_by_variant = data.variants.iter().enumerate().map(|(i, variant)| {
                let variant_name = &variant.ident;
                match &variant.fields {
                    Fields::Unnamed(..) => {
                        quote! {
                            Self::#variant_name(_) => Some(#i),
                        }
                    }
                    Fields::Unit => {
                        // NOTE: this has already been validated to conform to:
                        // first variant, and is `None` identifier
                        if i != 0 || !is_valid_none_identifier(variant_name) {
                            panic!("internal validation inconsistency; check proc derive macro");
                        }
                        quote! {
                            Self::None => Some(#i),
                        }
                    }
                    _ => unreachable!("other variants validated to not exist"),
                }
            });

            let chunks_impl = quote! {
                self.assemble_chunks()
            };
            let decoration_impl = quote! {
                fn decoration(&self) -> Option<usize> {
                    match self {
                        #(#decoration_by_variant)*
                    }
                }
            };
            (chunks_impl, Some(decoration_impl))
        }
        Data::Union(..) => unreachable!("data was already validated to exclude union types"),
    };

    quote! {
        impl #impl_generics ssz_rs::Chunkable for #name #ty_generics {
            fn chunks(&self) -> Result<Vec<u8>, ssz_rs::MerkleizationError> {
                #chunks_impl
            }

            #decoration_impl
        }
    }
}

fn derive_visitable_impl(data: &Data, name: &Ident, generics: &Generics) -> TokenStream {
    let (impl_generics, ty_generics, _) = generics.split_for_impl();

    let (visit_element_impl, element_count_impl) = match data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let fields = &fields.named;
                let field_count = fields.len();
                let impl_by_field = fields.iter().enumerate().map(|(i, field)| {
                    let field_name = field.ident.as_ref().expect("only named fields");
                    quote! {
                         #i => {
                            let child = &self.#field_name;
                            visitor.visit(child)
                        }
                    }
                });

                (
                    quote! {
                        if index >= #field_count {
                            Err(ssz_rs::VisitorError::InvalidInnerIndex.into())
                        } else {
                            match index {
                                #(#impl_by_field)*
                                _ => unreachable!("validated `index` to be within container type"),
                            }
                        }
                    },
                    quote! {
                        #field_count
                    },
                )
            }
            Fields::Unnamed(..) => {
                // NOTE: new type pattern, proxy to wrapped type...
                (
                    quote! {
                        self.0.visit_element(index, visitor)
                    },
                    quote! {
                        1
                    },
                )
            }
            Fields::Unit => unreachable!("validated to exclude this type"),
        },
        Data::Enum(ref data) => {
            let variant_count = data.variants.len();

            let impl_by_variant = data.variants.iter().enumerate().map(|(i, variant)| {
                let variant_name = &variant.ident;
                match &variant.fields {
                    Fields::Unnamed(..) => {
                        quote! {
                            Self::#variant_name(value) => visitor.visit(value),
                        }
                    }
                    Fields::Unit => {
                        // NOTE: this has already been validated to conform to:
                        // first variant, and is `None` identifier
                        if i != 0 || !is_valid_none_identifier(variant_name) {
                            panic!("internal validation inconsistency; check proc derive macro");
                        }

                        quote! {
                            Self::None => {
                                let leaf = 0usize;
                                visitor.visit(&leaf)
                            }
                        }
                    }
                    _ => unreachable!("other variants validated to not exist"),
                }
            });

            (
                quote! {
                    if index >= #variant_count {
                        Err(ssz_rs::VisitorError::InvalidInnerIndex.into())
                    } else {
                        match self {
                            #(#impl_by_variant)*
                        }
                    }
                },
                quote! {
                    #variant_count
                },
            )
        }
        Data::Union(..) => unreachable!("data was already validated to exclude union types"),
    };

    quote! {
        impl #impl_generics ssz_rs::Visitable for #name #ty_generics {
            fn visit_element<V: ssz_rs::Visitor>(
                &self,
                index: usize,
                visitor: &mut V,
            ) -> Result<(), V::Error> {
                #visit_element_impl
            }

            fn element_count(&self) -> usize {
                #element_count_impl
            }
        }
    }
}

fn is_valid_none_identifier(ident: &Ident) -> bool {
    *ident == format_ident!("None")
}

fn filter_ssz_attrs<'a>(
    attrs: impl Iterator<Item = &'a Attribute>,
) -> impl Iterator<Item = &'a Attribute> {
    attrs.filter(|&f| {
        if let Some(path) = f.path.segments.first() {
            path.ident == format_ident!("{SSZ_HELPER_ATTRIBUTE}")
        } else {
            false
        }
    })
}

fn validate_no_attrs<'a>(fields: impl Iterator<Item = &'a Field>) {
    let mut ssz_attrs = fields.flat_map(|field| filter_ssz_attrs(field.attrs.iter()));
    if ssz_attrs.next().is_some() {
        panic!("macro attribute `{SSZ_HELPER_ATTRIBUTE}` is only allowed at enum level")
    }
}

// Validates the incoming data follows the rules
// for mapping the Rust term to something that can
// implement the `SimpleSerialize` trait.
//
// Panics if validation fails which aborts the macro derivation.
fn validate_derive_input(data: &Data, helper_attrs: &[HelperAttr]) {
    if helper_attrs.len() > 1 {
        panic!("only one argument to the helper attribute is allowed")
    }
    let mut is_transparent = false;
    if let Some(attr) = helper_attrs.first() {
        match attr {
            HelperAttr::Transparent => is_transparent = true,
        }
    }
    if is_transparent && !matches!(data, Data::Enum(..)) {
        panic!("`transparent` option is only compatible with enums")
    }
    match data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                if fields.named.is_empty() {
                    panic!("ssz_rs containers with no fields are illegal")
                }
                validate_no_attrs(fields.named.iter())
            }
            Fields::Unnamed(ref fields) if fields.unnamed.len() == 1 => {
                validate_no_attrs(fields.unnamed.iter())
            }
            _ => panic!("structs with unit or multiple unnnamed fields are not supported"),
        },
        Data::Enum(ref data) => {
            if data.variants.is_empty() {
                panic!("SSZ unions must have at least 1 variant; this enum has none");
            }

            if data.variants.len() > 127 {
                panic!("SSZ unions cannot have more than 127 variants; this enum has more");
            }

            let mut none_forbidden = false;
            let mut already_has_none = false;
            for (i, variant) in data.variants.iter().enumerate() {
                let mut variant_ssz_attrs = filter_ssz_attrs(variant.attrs.iter());
                if variant_ssz_attrs.next().is_some() {
                    panic!("macro attribute `{SSZ_HELPER_ATTRIBUTE}` is only allowed at struct or enum level")
                }
                validate_no_attrs(variant.fields.iter());
                match &variant.fields {
                    Fields::Unnamed(inner) => {
                        if i == 0 {
                            none_forbidden = true;
                        }
                        if inner.unnamed.len() != 1 {
                            panic!("enums can only have 1 type per variant");
                        }
                        validate_no_attrs(inner.unnamed.iter());
                    }
                    Fields::Unit => {
                        if is_transparent {
                            panic!("`transparent` option is only compatible with unnamed variants")
                        }
                        if none_forbidden {
                            panic!(
                                "found unit variant that conflicts with previous unnamed variants"
                            );
                        }
                        if already_has_none {
                            panic!("cannot duplicate a unit variant (as only `None` is allowed)");
                        }
                        if !is_valid_none_identifier(&variant.ident) {
                            panic!("variant identifier is invalid: must be `None`");
                        }
                        if i != 0 {
                            panic!("only the first variant can be unit type (and must be `None`)")
                        }
                        if data.variants.len() < 2 {
                            panic!(
                                "SSZ unions must have more than 1 selector if the first is `None`"
                            );
                        }
                        already_has_none = true;
                    }
                    Fields::Named(..) => {
                        panic!("Enums with named fields in variants are not supported");
                    }
                };
            }
        }
        Data::Union(..) => panic!("Rust unions cannot produce valid SSZ types"),
    }
}

fn derive_serializable_impl(
    data: &Data,
    name: &Ident,
    generics: &Generics,
    helper_attr: Option<&HelperAttr>,
) -> proc_macro2::TokenStream {
    let serialize_impl = derive_serialize_impl(data, helper_attr);
    let deserialize_impl = derive_deserialize_impl(data, helper_attr);
    let is_variable_size_impl = derive_variable_size_impl(data);
    let size_hint_impl = derive_size_hint_impl(data);

    let (impl_generics, ty_generics, _) = generics.split_for_impl();
    quote! {
        impl #impl_generics ssz_rs::Serialize for #name #ty_generics {
            #serialize_impl
        }

        impl #impl_generics ssz_rs::Deserialize for #name #ty_generics {
            #deserialize_impl
        }

        impl #impl_generics ssz_rs::Serializable for #name #ty_generics {
            fn is_variable_size() -> bool {
                #is_variable_size_impl
            }

            fn size_hint() -> usize {
                #size_hint_impl
            }
        }
    }
}

fn derive_simple_serialize_impl(name: &Ident, generics: &Generics) -> proc_macro2::TokenStream {
    let (impl_generics, ty_generics, _) = generics.split_for_impl();

    quote! {
        impl #impl_generics ssz_rs::SimpleSerialize for #name #ty_generics {}
    }
}

#[derive(Debug, Clone, Copy)]
enum HelperAttr {
    Transparent,
}

fn parse_helper_attr(ident: &Ident) -> HelperAttr {
    match ident.to_string().as_str() {
        "transparent" => HelperAttr::Transparent,
        ident => panic!("unsupported helper attribute:{ident}"),
    }
}

fn extract_helper_attrs(input: &DeriveInput) -> Vec<HelperAttr> {
    filter_ssz_attrs(input.attrs.iter())
        .flat_map(|attr| {
            let meta = attr.parse_meta().unwrap();
            match meta {
                Meta::List(args) => args
                    .nested
                    .iter()
                    .map(|arg| match arg {
                        NestedMeta::Meta(meta) => {
                            if let Meta::Path(path) = meta {
                                assert!(path.leading_colon.is_none());
                                assert_eq!(path.segments.len(), 1);
                                let path = &path.segments[0];
                                match path.arguments {
                                    PathArguments::None => parse_helper_attr(&path.ident),
                                    _ => panic!("no arguments are supported to attribute symbols"),
                                }
                            } else {
                                panic!("unsupported argument to helper attribute");
                            }
                        }
                        _ => panic!("literals unsupported in attributes"),
                    })
                    .collect::<Vec<_>>(),
                _ => panic!("only list-like attributes are supported"),
            }
        })
        .collect()
}

/// Derive an implementation of the `Serializable` trait.
///
/// Includes the `Serialize` and `Deserialize` trait bounds.
/// Useful if you only want to encode or decode SSZ streams and do not need any Merkle tree
/// functionality.
#[proc_macro_derive(Serializable, attributes(ssz))]
pub fn derive_serializable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let data = &input.data;
    let helper_attrs = extract_helper_attrs(&input);
    validate_derive_input(data, &helper_attrs);
    let helper_attr = helper_attrs.first();

    let name = &input.ident;
    let generics = &input.generics;

    let expansion = derive_serializable_impl(data, name, generics, helper_attr);
    proc_macro::TokenStream::from(expansion)
}

/// Derive an implementation of the `HashTreeRoot` trait to support computation of the root of a
/// type's SSZ merkle tree.
#[proc_macro_derive(HashTreeRoot, attributes(ssz))]
pub fn derive_hash_tree_root(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let data = &input.data;
    let helper_attrs = extract_helper_attrs(&input);
    validate_derive_input(data, &helper_attrs);
    let helper_attr = helper_attrs.first();

    let name = &input.ident;
    let generics = &input.generics;

    let expansion = derive_merkleization_impl(data, name, generics, helper_attr);
    proc_macro::TokenStream::from(expansion)
}

/// Derive an implementation of the `GeneralizedIndexable` trait to support computation of
/// generalized indices.
#[proc_macro_derive(GeneralizedIndexable)]
pub fn derive_generalized_indexable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let data = &input.data;
    validate_derive_input(data, &[]);
    let name = &input.ident;
    let generics = &input.generics;

    let expansion = derive_generalized_indexable_impl(data, name, generics);
    proc_macro::TokenStream::from(expansion)
}

/// Derive an implementation of the `Chunkable` trait to support Merkle proofs.
#[proc_macro_derive(Chunkable)]
pub fn derive_chunkable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let data = &input.data;
    validate_derive_input(data, &[]);
    let name = &input.ident;
    let generics = &input.generics;

    let expansion = derive_chunkable_impl(data, name, generics);
    proc_macro::TokenStream::from(expansion)
}

/// Derive an implementation of the `Visitable` trait to support Merkle proofs.
#[proc_macro_derive(Visitable)]
pub fn derive_visitable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let data = &input.data;
    validate_derive_input(data, &[]);
    let name = &input.ident;
    let generics = &input.generics;

    let expansion = derive_visitable_impl(data, name, generics);
    proc_macro::TokenStream::from(expansion)
}

/// Derive `SimpleSerialize` for the attached item, including the relevant additional traits
/// required by the trait bound. Most common macro used from this crate.
#[proc_macro_derive(SimpleSerialize)]
pub fn derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let data = &input.data;
    validate_derive_input(data, &[]);

    let name = &input.ident;
    let generics = &input.generics;

    let serializable_impl = derive_serializable_impl(data, name, generics, None);

    let merkleization_impl = derive_merkleization_impl(data, name, generics, None);

    let generalized_indexable_impl = derive_generalized_indexable_impl(data, name, generics);

    let chunkable_impl = derive_chunkable_impl(data, name, generics);

    let visitable_impl = derive_visitable_impl(data, name, generics);

    let simple_serialize_impl = derive_simple_serialize_impl(name, generics);

    let expansion = quote! {
        #serializable_impl

        #merkleization_impl

        #generalized_indexable_impl

        #chunkable_impl

        #visitable_impl

        #simple_serialize_impl
    };

    proc_macro::TokenStream::from(expansion)
}
