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