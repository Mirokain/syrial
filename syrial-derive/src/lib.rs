// MIT License
// 
// Copyright (c) 2025 Mirokai Phoryvix
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.


extern crate proc_macro;

use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse_macro_input, DeriveInput, Data, Fields, Field};

#[proc_macro_derive(Serialize)]
pub fn derive_serialize(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let expanded = match &input.data {
        Data::Struct(data) => {
            let fields = match &data.fields {
                Fields::Named(fields) => &fields.named,
                _ => panic!("Only structs with named fields are supported"),
            };

            let serialize_fields = fields.iter().map(|f| {
                let field = f.ident.as_ref().expect("Named field should have identifier");
                quote! {
                    self.#field.serialize_into(stream);
                }
            });

            let serialize_size_fields = fields.iter().map(|f| {
                let field = f.ident.as_ref().expect("Named field should have identifier");
                quote! {
                    + self.#field.serialize_size()
                }
            });

            quote! {
                impl crate::serialize::Serialize for #name {
                    fn serialize(&self) -> crate::stream::Stream {
                        let mut stream = crate::stream::Stream::default();
                        self.serialize_into(&mut stream);
                        stream
                    }
                    
                    fn serialize_into(&self, stream: &mut crate::stream::Stream) {
                        #(#serialize_fields)*
                    }

                    fn serialize_size(&self) -> usize {
                        let mut size = 0;
                        #(size = size #serialize_size_fields;)*
                        size
                    }
                }
            }
        },
        Data::Enum(data) => {
            let variants = data.variants.iter().enumerate().map(|(i, v)| {
                let ident = &v.ident;
                let index = i as u8;
                quote! {
                    #name::#ident => #index
                }
            });

            quote! {
                impl crate::serialize::Serialize for #name {
                    fn serialize(&self) -> crate::stream::Stream {
                        let mut stream = crate::stream::Stream::default();
                        self.serialize_into(&mut stream);
                        stream
                    }
                    
                    fn serialize_into(&self, stream: &mut crate::stream::Stream) {
                        let value = match self {
                            #(#variants),*
                        };
                        stream.write(&[value]);
                    }

                    fn serialize_size(&self) -> usize {
                        std::mem::size_of::<u8>()
                    }
                }
            }
        }
        _ => panic!("Only structs and enums are supported"),
    };

    TokenStream::from(expanded)
}

#[proc_macro_derive(Deserialize)]
pub fn derive_deserialize(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let expanded = match &input.data {
        Data::Struct(data) => {
            let fields = match &data.fields {
                Fields::Named(fields) => &fields.named,
                _ => panic!("Only structs with named fields are supported"),
            };

            let deserialize_fields = fields.iter().map(|f| {
                let field = f.ident.as_ref().expect("Named field should have identifier");
                let ty = &f.ty;
                quote! {
                    #field: <#ty as crate::serialize::Deserialize>::deserialize(stream)?
                }
            });

            let deserialize_into_fields = fields.iter().map(|f| {
                let field = f.ident.as_ref().expect("Named field should have identifier");
                let ty = &f.ty;
                quote! {
                    self.#field = <#ty as crate::serialize::Deserialize>::deserialize(stream)?;
                }
            });

            quote! {
                impl crate::serialize::Deserialize for #name {
                    fn deserialize(stream: &mut crate::stream::Stream) -> crate::serialize::Result<Self> {
                        Ok(#name {
                            #(#deserialize_fields),*
                        })
                    }

                    fn deserialize_into(&mut self, stream: &mut crate::stream::Stream) -> crate::serialize::Result<()> {
                        #(#deserialize_into_fields)*
                        Ok(())
                    }
                }
            }
        },
        Data::Enum(data) => {
            let variants = data.variants.iter().enumerate().map(|(i, v)| {
                let ident = &v.ident;
                let index = i as u8;
                quote! {
                    #index => Ok(#name::#ident)
                }
            });

            quote! {
                impl crate::serialize::Deserialize for #name {
                    fn deserialize(stream: &mut crate::stream::Stream) -> crate::serialize::Result<Self> {
                        let mut buf = [0u8; 1];
                        stream.read(&mut buf).map_err(|e| crate::serialize::SerializationError::Io(e))?;
                        match buf[0] {
                            #(#variants,)*
                            _ => Err(crate::serialize::SerializationError::InvalidFormat),
                        }
                    }

                    fn deserialize_into(&mut self, stream: &mut crate::stream::Stream) -> crate::serialize::Result<()> {
                        *self = Self::deserialize(stream)?;
                        Ok(())
                    }
                }
            }
        }
        _ => panic!("Only structs and enums are supported"),
    };

    TokenStream::from(expanded)
}