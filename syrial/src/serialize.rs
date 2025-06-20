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
use std::collections::HashMap;
use crate::stream;

// Custom error type to represent different serialization and deserialization errors.
#[derive(Debug)]
pub enum SerializationError {
    // Error caused by I/O operations (e.g., reading or writing to a stream).
    Io(std::io::Error),
    // Error caused by invalid UTF-8 sequences when decoding strings.
    Utf8(std::string::FromUtf8Error),
    // Generic error indicating data format is invalid or unexpected.
    InvalidFormat,
}

// Implement user-friendly errors -> string
impl std::fmt::Display for SerializationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SerializationError::Io(err) => write!(f, "IO error: {}", err),
            SerializationError::Utf8(err) => write!(f, "UTF-8 decoding error: {}", err),
            SerializationError::InvalidFormat => write!(f, "Invalid data format"),
        }
    }
}

// Standar Error trait to allow chaining and compatibility with other Rust errors.
impl std::error::Error for SerializationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            SerializationError::Io(err) => Some(err),       // IO error is the source
            SerializationError::Utf8(err) => Some(err),     // UTF-8 error is the source
            SerializationError::InvalidFormat => None,      // no error for this variant
        }
    }
}

// Allow automatic conversion from std::io::Error into SerializationError::Io
impl From<std::io::Error> for SerializationError {
    fn from(err: std::io::Error) -> Self {
        SerializationError::Io(err)
    }
}

// Allow automatic conversion from std::string::FromUtf8Error into SerializationError::Utf8
impl From<std::string::FromUtf8Error> for SerializationError {
    fn from(err: std::string::FromUtf8Error) -> Self {
        SerializationError::Utf8(err)
    }
}

// Define a convenient alias for Result<T, SerializationError>
pub type Result<T> = std::result::Result<T, SerializationError>;


// Trait for types that can be serialized into a binary stream.
pub trait Serialize {
    // Convenience method to serialize the value into a new Stream and return it.
    fn serialize(&self) -> stream::Stream {
        let mut stream = stream::Stream::default();
        // Delegate actual serialization logic to serialize_into.
        self.serialize_into(&mut stream);
        stream
    }

    // Serialize the value directly into the provided stream.
    fn serialize_into(&self, stream: &mut stream::Stream);

    // Return the size in bytes the serialized value will occupy.
    fn serialize_size(&self) -> usize;
}

// Trait for types that can be deserialized from a binary stream.
pub trait Deserialize: Sized {
    // Create a new instance of the type by reading from the stream.
    fn deserialize(stream: &mut stream::Stream) -> Result<Self>;

    // Update an existing instance by reading its data from the stream.
    fn deserialize_into(&mut self, stream: &mut stream::Stream) -> Result<()>;
}



// Macro to define a default implementation of the `deserialize_into` method
// for types implementing the `Deserialize` trait.
//
// This method simply replaces `self` with a newly deserialized value from the stream.
macro_rules! impl_deserialize_into {
    () => {
        fn deserialize_into(&mut self, stream: &mut stream::Stream) -> Result<()> {
            *self = Self::deserialize(stream)?;
            Ok(())
        }
    };
}

// Macro to implement Serialize and Deserialize for primitive types
// that have fixed-size representations convertible to/from little-endian bytes.
macro_rules! serialize_primitive {
    ($t:ty, $write_fn:ident, $read_fn:ident) => {
        // Implement Serialize trait for type $t
        impl Serialize for $t {
            fn serialize_into(&self, stream: &mut stream::Stream) {
                // Convert the primitive value to little-endian bytes and write to the stream
                stream.write(&self.to_le_bytes());
            }

            fn serialize_size(&self) -> usize {
                // Size is the fixed size of the primitive type in bytes
                std::mem::size_of::<$t>()
            }
        }

        // Implement Deserialize trait for type $t
        impl Deserialize for $t {
            fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
                // Buffer to hold the bytes read from the stream, sized to the primitive
                let mut buf = [0u8; std::mem::size_of::<$t>()];
                // Read bytes into the buffer
                stream.read(&mut buf)?;
                // Convert from little-endian bytes to the primitive value
                Ok(Self::from_le_bytes(buf))
            }

            impl_deserialize_into!();
        }
    };
}


// Macro to implement Serialize and Deserialize traits for fixed-size arrays of u8 with length $len.
macro_rules! serialize_fixed_array {
    ($len:expr) => {
        // Implement Serialize for arrays of u8 of fixed length $len.
        impl Serialize for [u8; $len] {
            fn serialize_into(&self, stream: &mut stream::Stream) {
                // Write the entire fixed-size array to the stream in one go.
                stream.write(self);
            }
            fn serialize_size(&self) -> usize {
                // The serialized size is always the fixed length of the array.
                $len
            }
        }

        // Implement Deserialize for fixed-size arrays of u8 with length $len.
        impl Deserialize for [u8; $len] {
            fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
                // Create a zero-initialized array of length $len.
                let mut array = [0u8; $len];
                // Read exactly $len bytes from the stream into the array.
                stream.read(&mut array)?;
                // Return the filled array.
                Ok(array)
            }

            impl_deserialize_into!();
        }
    };
}



// Macro to implement Serialize and Deserialize traits for tuples of varying sizes.
// Accepts one or more tuple type parameter lists, e.g. (A), (A, B), (A, B, C), etc.
macro_rules! impl_serialize_tuple {
    // Pattern: one or more tuples, each with one or more generic type identifiers ($T).
    ($(($($T:ident),+)),+) => {
        $(
            // Implement Serialize trait for the tuple with generic types ($T).
            impl<$($T: Serialize),+> Serialize for ($($T),+,) {
                fn serialize_into(&self, stream: &mut stream::Stream) {
                    // Destructure self tuple into individual elements ($T).
                    let ($($T),+,) = self;
                    // Call serialize_into on each element, serializing them in order.
                    $($T.serialize_into(stream);)+
                }

                fn serialize_size(&self) -> usize {
                    let ($($T),+,) = self;
                    // Sum up the serialized sizes of all tuple elements.
                    0 $(+ $T.serialize_size())+
                }
            }

            // Implement Deserialize trait for the same tuple type.
            impl<$($T: Deserialize + Serialize),+> Deserialize for ($($T),+,) {
                fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
                    // Deserialize each element in order from the stream,
                    // collecting results into a tuple to return.
                    Ok((
                        $($T::deserialize(stream)?,)+
                    ))
                }

                impl_deserialize_into!();
            }
        )+
    };
}



/// Returns the size in bytes needed to serialize a given integer `n_size`
/// using a "compact size" variable-length encoding.
///
/// The encoding uses a prefix byte followed by 0, 2, 4, or 8 bytes depending
/// on the value of `n_size`. This optimizes space for small values.
///
/// # Parameters
/// - `n_size`: The integer value whose encoded size is to be calculated.
///
/// # Returns
/// The number of bytes required to store `n_size` in compact size format.
///
/// # Encoding scheme:
/// - If `n_size` is less than 253 (`u8::MAX - 2`), it fits in one byte.
/// - If <= `u16::MAX` (65535), it uses 1 prefix byte + 2 bytes.
/// - If <= `u32::MAX` (4,294,967,295), it uses 1 prefix byte + 4 bytes.
/// - Otherwise, uses 1 prefix byte + 8 bytes.
pub fn get_size_of_compact_size(n_size: u64) -> usize {
    if n_size < u8::MAX as u64 - 2 {
        // Fits in one byte
        std::mem::size_of::<u8>()
    } else if n_size <= u16::MAX as u64 {
        // Prefix byte + 2 bytes
        std::mem::size_of::<u8>() + std::mem::size_of::<u16>()
    } else if n_size <= u32::MAX as u64 {
        // Prefix byte + 4 bytes
        std::mem::size_of::<u8>() + std::mem::size_of::<u32>()
    } else {
        // Prefix byte + 8 bytes
        std::mem::size_of::<u8>() + std::mem::size_of::<u64>()
    }
}


/// Writes the integer `n` into the stream using a compact size encoding.
///
/// This encoding uses a variable-length format to minimize the number of bytes
/// needed to represent the number. It writes a prefix byte followed by 0, 2, 4,
/// or 8 bytes depending on the size of `n`.
///
/// # Parameters
/// - `stream`: The output stream to write bytes into.
/// - `n`: The unsigned 64-bit integer to encode.
///
/// # Encoding scheme:
/// - If `n` is less than 251 (`u8::MAX - 2`), write `n` directly as a single byte.
/// - If `n` fits in a `u16`, write the prefix byte 251 (`u8::MAX - 2`), then the
///   lower 2 bytes of `n` in little-endian order.
/// - If `n` fits in a `u32`, write the prefix byte 252 (`u8::MAX - 1`), then the
///   lower 4 bytes of `n` in little-endian order.
/// - Otherwise, write the prefix byte 253 (`u8::MAX`), then all 8 bytes of `n`
///   in little-endian order.
pub fn write_compact_size(stream: &mut stream::Stream, n: u64) {
    if n < u8::MAX as u64 - 2 {
        // For small values, write just one byte directly.
        stream.write(&[n as u8]);
    } else if n <= u16::MAX as u64 {
        // Prefix 251 indicates next 2 bytes hold the value.
        stream.write(&[u8::MAX - 2]);
        stream.write(&n.to_le_bytes()[..2]);  // Write lower 2 bytes (little endian)
    } else if n <= u32::MAX as u64 {
        // Prefix 252 indicates next 4 bytes hold the value.
        stream.write(&[u8::MAX - 1]);
        stream.write(&n.to_le_bytes()[..4]);  // Write lower 4 bytes
    } else {
        // Prefix 253 indicates next 8 bytes hold the value.
        stream.write(&[u8::MAX]);
        stream.write(&n.to_le_bytes());       // Write full 8 bytes
    }
}


/// Reads an unsigned 64-bit integer from the stream that was encoded
/// using the compact size variable-length encoding.
///
/// The function reads a prefix byte first, then reads additional bytes
/// depending on the prefix, reconstructing the original number.
///
/// # Parameters
/// - `stream`: The input stream to read bytes from.
///
/// # Returns
/// - `Ok(u64)` with the decoded number on success.
/// - An error if reading from the stream fails.
///
/// # Decoding scheme:
/// - If the prefix byte is less than 251 (`u8::MAX - 2`), it represents the number directly.
/// - If the prefix byte is 251 (`u8::MAX - 2`), read the next 2 bytes and decode as `u16`.
/// - If the prefix byte is 252 (`u8::MAX - 1`), read the next 4 bytes and decode as `u32`.
/// - Otherwise, read the next 8 bytes and decode as `u64`.
pub fn read_compact_size(stream: &mut stream::Stream) -> Result<u64> {
    let mut ch_size = [0u8; 1];
    stream.read(&mut ch_size)?;  // Read prefix byte

    match ch_size[0] {
        // If prefix is less than 251, it *is* the number
        ch if ch < u8::MAX - 2 => Ok(ch as u64),

        // If prefix == 251, read 2 bytes and convert to u16
        ch if ch == u8::MAX - 2 => {
            let mut size = [0u8; 2];
            stream.read(&mut size)?;
            Ok(u16::from_le_bytes(size) as u64)
        }

        // If prefix == 252, read 4 bytes and convert to u32
        ch if ch == u8::MAX - 1 => {
            let mut size = [0u8; 4];
            stream.read(&mut size)?;
            Ok(u32::from_le_bytes(size) as u64)
        }

        // Otherwise, read 8 bytes and convert to u64
        _ => {
            let mut size = [0u8; 8];
            stream.read(&mut size)?;
            Ok(u64::from_le_bytes(size))
        }
    }
}


// Serialize implementation for HashMap<K, V>
// where K and V both implement Serialize.
impl<K: Serialize, V: Serialize> Serialize for HashMap<K, V> {
    fn serialize_into(&self, stream: &mut stream::Stream) {
        // First write the number of key-value pairs using compact size encoding.
        write_compact_size(stream, self.len() as u64);
        // Then serialize each key and value in order.
        for (key, value) in self {
            key.serialize_into(stream);
            value.serialize_into(stream);
        }
    }

    fn serialize_size(&self) -> usize {
        // Size of the compact size encoding for length +
        // sum of sizes of serialized keys and values.
        get_size_of_compact_size(self.len() as u64)
            + self.iter().map(|(k, v)| k.serialize_size() + v.serialize_size()).sum::<usize>()
    }
}

// Deserialize implementation for HashMap<K, V>
// where K and V implement Deserialize and Serialize,
// and K must also implement Eq and Hash for HashMap.
impl<K: Deserialize + Serialize + Eq + std::hash::Hash, V: Deserialize + Serialize> Deserialize for HashMap<K, V> {
    fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
        // Read the number of key-value pairs from the stream.
        let size = read_compact_size(stream)? as usize;
        // Pre-allocate HashMap with capacity.
        let mut map = HashMap::with_capacity(size);
        // For each entry, deserialize key and value and insert into map.
        for _ in 0..size {
            let key = K::deserialize(stream)?;
            let value = V::deserialize(stream)?;
            map.insert(key, value);
        }
        Ok(map)
    }

    impl_deserialize_into!();
}

// Serialize implementation for Vec<T> where T implements Serialize.
impl<T: Serialize> Serialize for Vec<T> {
    fn serialize_into(&self, stream: &mut stream::Stream) {
        // Write the length of the vector first (compact size).
        write_compact_size(stream, self.len() as u64);
        // Serialize each element in the vector.
        for item in self {
            item.serialize_into(stream);
        }
    }

    fn serialize_size(&self) -> usize {
        // Size of length prefix + sum of serialized sizes of elements.
        get_size_of_compact_size(self.len() as u64)
            + self.iter().map(|item| item.serialize_size()).sum::<usize>()
    }
}


// Deserialize implementation for Vec<T> where T implements Deserialize + Serialize.
impl<T: Deserialize + Serialize> Deserialize for Vec<T> {
    fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
        // Read the length of the vector from the stream.
        let size = read_compact_size(stream)? as usize;
        // Pre-allocate a vector with the given capacity.
        let mut vec = Vec::with_capacity(size);
        // Deserialize each item and push it into the vector.
        for _ in 0..size {
            let item = T::deserialize(stream)?;
            vec.push(item);
        }
        Ok(vec)
    }

    impl_deserialize_into!();
}

// Serialize implementation for String.
impl Serialize for String {
    fn serialize_into(&self, stream: &mut stream::Stream) {
        // Write the length of the string bytes as a compact size.
        write_compact_size(stream, self.len() as u64);
        // Write the string bytes to the stream.
        stream.write(self.as_bytes());
    }

    fn serialize_size(&self) -> usize {
        // Size for the length prefix + number of bytes in the string.
        get_size_of_compact_size(self.len() as u64) + self.len()
    }
}

// Deserialize implementation for String.
impl Deserialize for String {
    fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
        // Read the length of the string bytes.
        let size = read_compact_size(stream)? as usize;
        // Allocate a buffer of the required size.
        let mut buffer = vec![0; size];
        // Read the bytes from the stream.
        stream.read(&mut buffer)?;
        // Convert bytes to UTF-8 string (error if invalid UTF-8).
        Ok(String::from_utf8(buffer)?)
    }

    impl_deserialize_into!();
}


/// Macro to implement Serialize and Deserialize for types
/// that can be converted to/from a String via `ToString` and `FromStr`.
///
/// This allows any type that implements `ToString` (for serialization)
/// and `FromStr` (for deserialization) to be easily supported.
macro_rules! impl_serialize_for_to_string {
    ($t:path) => {
        impl Serialize for $t {
            fn serialize_into(&self, stream: &mut stream::Stream) {
                // Convert the value to a String and serialize the String.
                self.to_string().serialize_into(stream)
            }

            fn serialize_size(&self) -> usize {
                // Get the size of the serialized string representation.
                self.to_string().serialize_size()
            }
        }

        impl Deserialize for $t {
            fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
                // Deserialize a String from the stream.
                let s = String::deserialize(stream)?;
                // Parse the String into the target type.
                // Return an error if parsing fails.
                s.parse().map_err(|_| SerializationError::InvalidFormat)
            }

            impl_deserialize_into!();
        }
    };
}


impl<T: Serialize> Serialize for Option<T> {
    fn serialize_into(&self, stream: &mut stream::Stream) {
        match self {
            Some(val) => {
                // Write a tag byte '1' to indicate presence of a value
                1u8.serialize_into(stream);
                // Serialize the contained value
                val.serialize_into(stream);
            }
            None => {
                // Write a tag byte '0' to indicate None (no value)
                0u8.serialize_into(stream);
            }
        }
    }

    fn serialize_size(&self) -> usize {
        // Always 1 byte for the tag plus the size of the contained value if Some
        1 + match self {
            Some(val) => val.serialize_size(),
            None => 0,
        }
    }
}

impl<T: Deserialize> Deserialize for Option<T> {
    fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
        // Read the tag byte to determine if there is a value
        let tag = u8::deserialize(stream)?;
        match tag {
            0 => Ok(None),                    // Tag 0 means None
            1 => Ok(Some(T::deserialize(stream)?)), // Tag 1 means Some, so deserialize the value
            _ => Err(SerializationError::InvalidFormat), // Any other tag is invalid
        }
    }

    impl_deserialize_into!();
}


impl Serialize for bool {
    fn serialize_into(&self, stream: &mut stream::Stream) {
        // Write a single byte to the stream:
        // 1 for true, 0 for false
        stream.write(&[if *self { 1 } else { 0 }]);
    }

    fn serialize_size(&self) -> usize {
        // Always 1 byte is needed to serialize a bool
        1
    }
}

impl Deserialize for bool {
    fn deserialize(stream: &mut stream::Stream) -> Result<Self> {
        let mut buf = [0u8; 1];
        // Read exactly one byte from the stream
        stream.read(&mut buf)?;
        // Interpret the byte:
        // 0 means false, 1 means true
        // Any other value is invalid and returns an error
        match buf[0] {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(SerializationError::InvalidFormat),
        }
    }

    impl_deserialize_into!();
}


// Implement Serialize and Deserialize for primitive numeric types.
// The macro `serialize_primitive!` takes three arguments:
// 1. The Rust primitive type,
// 2. The function to write (serialize) that type to the stream,
// 3. The function to read (deserialize) that type from the stream.
serialize_primitive!(u8, write_u8, read_u8);
serialize_primitive!(i8, write_i8, read_i8);
serialize_primitive!(u16, write_u16, read_u16);
serialize_primitive!(i16, write_i16, read_i16);
serialize_primitive!(u32, write_u32, read_u32);
serialize_primitive!(i32, write_i32, read_i32);
serialize_primitive!(u64, write_u64, read_u64);
serialize_primitive!(i64, write_i64, read_i64);
serialize_primitive!(f32, write_f32, read_f32);
serialize_primitive!(f64, write_f64, read_f64);

// Implement Serialize and Deserialize for fixed-size arrays of bytes.
// The macro `serialize_fixed_array!` supports fixed-length arrays of the specified size.
serialize_fixed_array!(4);
serialize_fixed_array!(8);
serialize_fixed_array!(12);
serialize_fixed_array!(16);
serialize_fixed_array!(32);
serialize_fixed_array!(64);
serialize_fixed_array!(128);

// Implement Serialize and Deserialize for tuples of varying sizes.
// The macro `impl_serialize_tuple!` is called with tuples of generic types,
// supporting tuples with 1 to 10 elements here.
impl_serialize_tuple!(
    (A),
    (A, B),
    (A, B, C),
    (A, B, C, D),
    (A, B, C, D, E),
    (A, B, C, D, E, F),
    (A, B, C, D, E, F, G),
    (A, B, C, D, E, F, G, H),
    (A, B, C, D, E, F, G, H, I),
    (A, B, C, D, E, F, G, H, I, J)
);



#[cfg(test)]
mod tests {
    use super::*;
    use crate::stream::Stream;
    use crate::serialize::{Serialize, Deserialize};

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

    fn sample_test(i: i32) -> Test {
        Test {
            int_val: i,
            bool_val: i % 2 == 0,
            string_val: format!("test_{i}"),
            vec_val: vec![i as u8, (i + 1) as u8],
            tuple_val: (i as u8, format!("tuple_{i}")),
            array_val: [i as u8, i as u8, i as u8, i as u8],
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

        let val_f32: f32 = 3.14159;
        let mut stream = Stream::default();
        val_f32.serialize_into(&mut stream);
        let result = f32::deserialize(&mut stream).unwrap();
        assert_eq!(val_f32, result);

        let mut val_f32_serialized = val_f32.serialize();
        let val_f32_deserialized = f32::deserialize(&mut val_f32_serialized).unwrap();
        assert_eq!(val_f32, val_f32_deserialized);

        let val_f64: f64 = -2.71828;
        let mut stream = Stream::default();
        val_f64.serialize_into(&mut stream);
        let result = f64::deserialize(&mut stream).unwrap();
        assert_eq!(val_f64, result);

        let mut val_f64_serialized = val_f64.serialize();
        let val_f64_deserialized = f64::deserialize(&mut val_f64_serialized).unwrap();
        assert_eq!(val_f64, val_f64_deserialized);
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

    #[test]
    fn test_option_some_and_none() {
        let val_none: Option<u32> = None;
        let mut stream_none = Stream::default();
        val_none.serialize_into(&mut stream_none);
        let deserialized_none = Option::<u32>::deserialize(&mut stream_none).unwrap();
        assert_eq!(val_none, deserialized_none);

        let val_some: Option<u32> = Some(12345);
        let mut stream_some = Stream::default();
        val_some.serialize_into(&mut stream_some);
        let deserialized_some = Option::<u32>::deserialize(&mut stream_some).unwrap();
        assert_eq!(val_some, deserialized_some);
    }

    #[test]
    fn test_hashmap() {
        let mut map = HashMap::new();
        map.insert(1u8, String::from("one"));
        map.insert(2u8, String::from("two"));
        let mut stream = Stream::default();
        map.serialize_into(&mut stream);
        let result = HashMap::<u8, String>::deserialize(&mut stream).unwrap();
        assert_eq!(map, result);
    }

    #[test]
    fn test_5_tuples() {
        let tuple = (
            sample_test(100),
            sample_test(101),
            sample_test(102),
            sample_test(103),
            sample_test(104),
        );

        let mut stream = Stream::default();
        tuple.serialize_into(&mut stream);

        let deserialized: (Test, Test, Test, Test, Test) =
        <(Test, Test, Test, Test, Test)>::deserialize(&mut stream).unwrap();

        assert_eq!(tuple, deserialized);

    }
}