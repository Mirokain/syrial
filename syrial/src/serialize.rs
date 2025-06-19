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


use std::io::{Read, Write};
use crate::stream;

#[derive(Debug)]
pub enum SerializationError {
    Io(std::io::Error),
    Utf8(std::string::FromUtf8Error),
    InvalidFormat,
}

impl std::fmt::Display for SerializationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SerializationError::Io(err) => write!(f, "IO error: {}", err),
            SerializationError::Utf8(err) => write!(f, "UTF-8 decoding error: {}", err),
            SerializationError::InvalidFormat => write!(f, "Invalid data format"),
        }
    }
}

impl std::error::Error for SerializationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            SerializationError::Io(err) => Some(err),
            SerializationError::Utf8(err) => Some(err),
            SerializationError::InvalidFormat => None,
        }
    }
}

impl From<std::io::Error> for SerializationError {
    fn from(err: std::io::Error) -> Self {
        SerializationError::Io(err)
    }
}

impl From<std::string::FromUtf8Error> for SerializationError {
    fn from(err: std::string::FromUtf8Error) -> Self {
        SerializationError::Utf8(err)
    }
}

pub type Result<T> = std::result::Result<T, SerializationError>;

pub trait Serialize {
    fn serialize(&self) -> stream::Stream {
        let mut stream = stream::Stream::default();
        self.serialize_into(&mut stream);
        stream
    }

    fn serialize_into(&self, stream: &mut stream::Stream);
    fn serialize_size(&self) -> usize;
}

pub trait Deserialize: Sized {
    fn deserialize(stream: &mut stream::Stream) -> Result<Self>;
    fn deserialize_into(&mut self, stream: &mut stream::Stream) -> Result<()>;
}

macro_rules! serialize_primitive {
    ($t:ty, $write_fn:ident, $read_fn:ident) => {
        impl Serialize for $t {
            fn serialize_into(&self, stream: &mut stream::Stream) {
                stream.write(&self.to_le_bytes());
            }
            fn serialize_size(&self) -> usize {
                std::mem::size_of::<$t>()
            }
        }

        impl Deserialize for $t {
            fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
                let mut buf = [0u8; std::mem::size_of::<$t>()];
                stream.read(&mut buf)?;
                Ok(Self::from_le_bytes(buf))
            }

            fn deserialize_into(&mut self, stream: &mut stream::Stream) -> Result<()> {
                *self = Self::deserialize(stream)?;
                Ok(())
            }
        }
    };
}

macro_rules! serialize_fixed_array {
    ($len:expr) => {
        impl Serialize for [u8; $len] {
            fn serialize_into(&self, stream: &mut stream::Stream) {
                stream.write(self);
            }
            fn serialize_size(&self) -> usize {
                $len
            }
        }

        impl Deserialize for [u8; $len] {
            fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
                let mut array = [0u8; $len];
                stream.read(&mut array)?;
                Ok(array)
            }

            fn deserialize_into(&mut self, stream: &mut stream::Stream) -> Result<()> {
                *self = Self::deserialize(stream)?;
                Ok(())
            }
        }
    };
}

impl<T: Serialize> Serialize for (T,) {
    fn serialize_into(&self, stream: &mut stream::Stream) {
        self.0.serialize_into(stream);
    }

    fn serialize_size(&self) -> usize {
        self.0.serialize_size()
    }
}

impl<T: Deserialize + Serialize> Deserialize for (T,) {
    fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
        let first = T::deserialize(stream)?;
        Ok((first,))
    }

    fn deserialize_into(&mut self, stream: &mut stream::Stream) -> Result<()> {
        *self = <(T,)>::deserialize(stream)?;
        Ok(())
    }
}

pub fn get_size_of_compact_size(n_size: u64) -> usize {
    if n_size < u8::MAX as u64 - 2 {
        std::mem::size_of::<u8>()
    } else if n_size <= u16::MAX as u64 {
        std::mem::size_of::<u8>() + std::mem::size_of::<u16>()
    } else if n_size <= u32::MAX as u64 {
        std::mem::size_of::<u8>() + std::mem::size_of::<u32>()
    } else {
        std::mem::size_of::<u8>() + std::mem::size_of::<u64>()
    }
}

pub fn write_compact_size(stream: &mut stream::Stream, n: u64) {
    if n < u8::MAX as u64 - 2 {
        stream.write(&[n as u8]);
    } else if n <= u16::MAX as u64 {
        stream.write(&[u8::MAX - 2]);
        stream.write(&n.to_le_bytes()[..2]);
    } else if n <= u32::MAX as u64 {
        stream.write(&[u8::MAX - 1]);
        stream.write(&n.to_le_bytes()[..4]);
    } else {
        stream.write(&[u8::MAX]);
        stream.write(&n.to_le_bytes());
    }
}

pub fn read_compact_size(stream: &mut stream::Stream) -> Result<u64> {
    let mut ch_size = [0u8; 1];
    stream.read(&mut ch_size)?;
    match ch_size[0] {
        ch if ch < u8::MAX - 2 => Ok(ch as u64),
        ch if ch == u8::MAX - 2 => {
            let mut size = [0u8; 2];
            stream.read(&mut size)?;
            Ok(u16::from_le_bytes(size) as u64)
        }
        ch if ch == u8::MAX - 1 => {
            let mut size = [0u8; 4];
            stream.read(&mut size)?;
            Ok(u32::from_le_bytes(size) as u64)
        }
        _ => {
            let mut size = [0u8; 8];
            stream.read(&mut size)?;
            Ok(u64::from_le_bytes(size))
        }
    }
}

impl<T: Serialize> Serialize for Vec<T> {
    fn serialize_into(&self, stream: &mut stream::Stream) {
        write_compact_size(stream, self.len() as u64);
        for item in self {
            item.serialize_into(stream);
        }
    }

    fn serialize_size(&self) -> usize {
        get_size_of_compact_size(self.len() as u64) + self.iter().map(|item| item.serialize_size()).sum::<usize>()
    }
}

impl<T: Deserialize + Serialize> Deserialize for Vec<T> {
    fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
        let size = read_compact_size(stream)? as usize;
        let mut vec = Vec::with_capacity(size);
        for _ in 0..size {
            let item = T::deserialize(stream)?;
            vec.push(item);
        }
        Ok(vec)
    }

    fn deserialize_into(&mut self, stream: &mut stream::Stream) -> Result<()> {
        *self = Self::deserialize(stream)?;
        Ok(())
    }
}

impl Serialize for String {
    fn serialize_into(&self, stream: &mut stream::Stream) {
        write_compact_size(stream, self.len() as u64);
        stream.write(self.as_bytes());
    }

    fn serialize_size(&self) -> usize {
        get_size_of_compact_size(self.len() as u64) + self.len()
    }
}

impl Deserialize for String {
    fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
        let size = read_compact_size(stream)? as usize;
        let mut buffer = vec![0; size];
        stream.read(&mut buffer)?;
        Ok(String::from_utf8(buffer)?)
    }

    fn deserialize_into(&mut self, stream: &mut stream::Stream) -> Result<()> {
        *self = Self::deserialize(stream)?;
        Ok(())
    }
}


macro_rules! impl_serialize_for_to_string {
    ($t:path) => {
        impl Serialize for $t {
            fn serialize_into(&self, stream: &mut stream::Stream) {
                self.to_string().serialize_into(stream)
            }

            fn serialize_size(&self) -> usize {
                self.to_string().serialize_size()
            }
        }

        impl Deserialize for $t {
            fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
                let s = String::deserialize(stream)?;
                s.parse().map_err(|_| SerializationError::InvalidFormat)
            }

            fn deserialize_into(&mut self, stream: &mut stream::Stream) -> Result<()> {
                *self = Self::deserialize(stream)?;
                Ok(())
            }
        }
    };
}



impl<K: Serialize, V: Serialize> Serialize for (K, V) {
    fn serialize_into(&self, stream: &mut stream::Stream) {
        self.0.serialize_into(stream);
        self.1.serialize_into(stream);
    }

    fn serialize_size(&self) -> usize {
        self.0.serialize_size() + self.1.serialize_size()
    }
}

impl<K: Deserialize + Serialize, V: Deserialize + Serialize> Deserialize for (K, V) {
    fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
        let first = K::deserialize(stream)?;
        let second = V::deserialize(stream)?;
        Ok((first, second))
    }

    fn deserialize_into(&mut self, stream: &mut stream::Stream) -> Result<()> {
        *self = Self::deserialize(stream)?;
        Ok(())
    }
}

impl Serialize for bool {
    fn serialize_into(&self, stream: &mut stream::Stream) {
        stream.write(&[if *self { 1 } else { 0 }]);
    }

    fn serialize_size(&self) -> usize {
        1
    }
}

impl Deserialize for bool {
    fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
        let mut buf = [0u8; 1];
        stream.read(&mut buf)?;
        match buf[0] {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(SerializationError::InvalidFormat),
        }
    }

    fn deserialize_into(&mut self, stream: &mut stream::Stream) -> Result<()> {
        *self = Self::deserialize(stream)?;
        Ok(())
    }
}

serialize_primitive!(u8, write_u8, read_u8);
serialize_primitive!(i8, write_i8, read_i8);
serialize_primitive!(u16, write_u16, read_u16);
serialize_primitive!(i16, write_i16, read_i16);
serialize_primitive!(u32, write_u32, read_u32);
serialize_primitive!(i32, write_i32, read_i32);
serialize_primitive!(u64, write_u64, read_u64);
serialize_primitive!(i64, write_i64, read_i64);

serialize_fixed_array!(4);
serialize_fixed_array!(8);
serialize_fixed_array!(12);
serialize_fixed_array!(16);
serialize_fixed_array!(32);
serialize_fixed_array!(64);
serialize_fixed_array!(128);

impl Serialize for () {
    fn serialize_into(&self, _stream: &mut stream::Stream) {}
    fn serialize_size(&self) -> usize { 0 }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stream::Stream;
    use crate::serialize::{Serialize, Deserialize}; // Fixed import

    #[derive(Debug, PartialEq)]
    pub struct Test {
        pub int_val: i32,
        pub bool_val: bool,
        pub string_val: String,
        pub vec_val: Vec<u8>,
        pub tuple_val: (u8, String),
        pub array_val: [u8; 4],
    }

    impl Serialize for Test {
        fn serialize_into(&self, stream: &mut Stream) {
            self.int_val.serialize_into(stream);
            self.bool_val.serialize_into(stream);
            self.string_val.serialize_into(stream);
            self.vec_val.serialize_into(stream);
            self.tuple_val.serialize_into(stream);
            self.array_val.serialize_into(stream);
        }

        fn serialize_size(&self) -> usize {
            self.int_val.serialize_size()
                + self.bool_val.serialize_size()
                + self.string_val.serialize_size()
                + self.vec_val.serialize_size()
                + self.tuple_val.serialize_size()
                + self.array_val.serialize_size()
        }
    }

    impl Deserialize for Test {
        fn deserialize(stream: &mut Stream) -> Result<Self> {
            Ok(Test {
                int_val: i32::deserialize(stream)?,
                bool_val: bool::deserialize(stream)?,
                string_val: String::deserialize(stream)?,
                vec_val: Vec::<u8>::deserialize(stream)?,
                tuple_val: <(u8, String)>::deserialize(stream)?,
                array_val: <[u8; 4]>::deserialize(stream)?,
            })
        }

        fn deserialize_into(&mut self, stream: &mut Stream) -> Result<()> {
            *self = Self::deserialize(stream)?;
            Ok(())
        }
    }

    #[test]
    fn test_primitives() {
        let val_u8: u8 = 42;
        let mut stream = Stream::default();
        val_u8.serialize_into(&mut stream);
        let result = u8::deserialize(&mut stream).unwrap();
        assert_eq!(val_u8, result);

        let mut val_u8_serialized = val_u8.serialize();
        let val_u8_deserialized = u8::deserialize(&mut val_u8_serialized).unwrap();
        assert_eq!(val_u8, val_u8_deserialized);

        let val_i32: i32 = -12345;
        let mut stream = Stream::default();
        val_i32.serialize_into(&mut stream);
        let result = i32::deserialize(&mut stream).unwrap();
        assert_eq!(val_i32, result);

        let mut val_i32_serialized = val_i32.serialize();
        let val_i32_deserialized = i32::deserialize(&mut val_i32_serialized).unwrap();
        assert_eq!(val_i32, val_i32_deserialized);

        let val_bool = true;
        let mut stream = Stream::default();
        val_bool.serialize_into(&mut stream);
        let result = bool::deserialize(&mut stream).unwrap();
        assert_eq!(val_bool, result);

        let mut val_bool_serialized = val_bool.serialize();
        let val_bool_deserialized = bool::deserialize(&mut val_bool_serialized).unwrap();
        assert_eq!(val_bool, val_bool_deserialized);
    }

    #[test]
    fn test_string() {
        let s = String::from("hello world");
        let mut stream = Stream::default();
        s.serialize_into(&mut stream);
        let result = String::deserialize(&mut stream).unwrap();
        assert_eq!(s, result);

        let mut s_serialized = s.serialize();
        let s_deserialized = String::deserialize(&mut s_serialized).unwrap();
        assert_eq!(s, s_deserialized);
    }

    #[test]
    fn test_vec() {
        let vec = vec![1u8, 2, 3, 4, 5];
        let mut stream = Stream::default();
        vec.serialize_into(&mut stream);
        let result = Vec::<u8>::deserialize(&mut stream).unwrap();
        assert_eq!(vec, result);

        let mut vec_serialized = vec.serialize();
        let vec_deserialized = Vec::<u8>::deserialize(&mut vec_serialized).unwrap();
        assert_eq!(vec, vec_deserialized);
    }

    #[test]
    fn test_tuple() {
        let tuple = (42u8, String::from("tuple"));
        let mut stream = Stream::default();
        tuple.serialize_into(&mut stream);
        let result = <(u8, String)>::deserialize(&mut stream).unwrap();
        assert_eq!(tuple, result);

        let mut tuple_serialized = tuple.serialize();
        let tuple_deserialized = <(u8, String)>::deserialize(&mut tuple_serialized).unwrap();
        assert_eq!(tuple, tuple_deserialized);
    }

    #[test]
    fn test_fixed_array() {
        let arr: [u8; 4] = [1, 2, 3, 4];
        let mut stream = Stream::default();
        arr.serialize_into(&mut stream);
        let result = <[u8; 4]>::deserialize(&mut stream).unwrap();
        assert_eq!(arr, result);

        let mut arr_serialized = arr.serialize();
        let arr_deserialized = <[u8; 4]>::deserialize(&mut arr_serialized).unwrap();
        assert_eq!(arr, arr_deserialized);
    }

    #[test]
    fn test_compact_size() {
        let mut stream = Stream::default();
        write_compact_size(&mut stream, 300);
        let result = read_compact_size(&mut stream).unwrap();
        assert_eq!(300, result);

        let mut stream = Stream::default();
        write_compact_size(&mut stream, u64::MAX);
        let result = read_compact_size(&mut stream).unwrap();
        assert_eq!(u64::MAX, result);
    }

    #[test]
    fn test_invalid_bool() {
        let mut stream = Stream::default();
        stream.write(&[5]);
        let result = bool::deserialize(&mut stream);
        assert!(matches!(result, Err(SerializationError::InvalidFormat)));
    }

    #[test]
    fn test_empty_vec() {
        let vec: Vec<u8> = vec![];
        let mut stream = Stream::default();
        vec.serialize_into(&mut stream);
        let result = Vec::<u8>::deserialize(&mut stream).unwrap();
        assert_eq!(vec, result);

        let mut vec_serialized = vec.serialize();
        let vec_deserialized = Vec::<u8>::deserialize(&mut vec_serialized).unwrap();
        assert_eq!(vec, vec_deserialized);
    }

    #[test]
    fn test_large_string() {
        let s = "a".repeat(10_000);
        let mut stream = Stream::default();
        s.serialize_into(&mut stream);
        let result = String::deserialize(&mut stream).unwrap();
        assert_eq!(s, result);

        let mut s_serialized = s.serialize();
        let s_deserialized = String::deserialize(&mut s_serialized).unwrap();
        assert_eq!(s, s_deserialized);
    }

    #[test]
    fn test_large_vec() {
        let vec: Vec<u32> = (0..1_000).collect();
        let mut stream = Stream::default();
        vec.serialize_into(&mut stream);
        let result = Vec::<u32>::deserialize(&mut stream).unwrap();
        assert_eq!(vec, result);

        let mut vec_serialized = vec.serialize();
        let vec_deserialized = Vec::<u32>::deserialize(&mut vec_serialized).unwrap();
        assert_eq!(vec, vec_deserialized);
    }

    #[test]
    fn test_impl_serialize_for_to_string() {
        use std::net::IpAddr;
        impl_serialize_for_to_string!(IpAddr);

        let ip: IpAddr = "127.0.0.1".parse().unwrap();
        let mut ip_serialized = ip.serialize();
        let ip_recovered: IpAddr = IpAddr::deserialize(&mut ip_serialized).unwrap();
        assert_eq!(ip, ip_recovered);
    }
}