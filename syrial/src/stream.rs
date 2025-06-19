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

use std::ops::Add;
use std::io;
use std::io::{Error, ErrorKind};

use crate::serialize::{Serialize, Deserialize};

#[derive(Debug, Clone)]
pub struct Stream {
    pub data: Vec<u8>,
    pub cursor: usize,
}

impl Stream {
    pub fn new(s: Vec<u8>) -> Stream {
        Stream {
            data: s,
            cursor: 0,
        }
    }

    pub fn copy(&self) -> Stream {
        Stream::new(self.data.clone())
    }

    pub fn to_string(&self) -> String {
        String::from_utf8_lossy(&self.data[self.cursor..]).to_string()
    }

    pub fn len(&self) -> usize {
        self.size()
    }

    pub fn find_str(&mut self, target: &str) -> bool {
        let target_bytes = target.as_bytes();
        let remaining_data = &self.data[self.cursor..];
        remaining_data.windows(target_bytes.len()).any(|window| window == target_bytes)
    }

    pub fn write(&mut self, s: &[u8]) {
        self.data.extend_from_slice(s);
    }

    pub fn write_data(&mut self, s: &[u8]) {
        self.seek_to_end();
        self.data.extend_from_slice(s);
    }

    pub fn write_str(&mut self, s: &str) {
        let current_pos = self.cursor;
        self.seek_to_end();
        self.data.extend_from_slice(s.as_bytes());
        self.seek(current_pos as u64);
    }

    pub fn raw_write(&mut self, s: &[u8], pos: usize) {
        let original_pos = self.cursor;
        let mut data = self.data.clone();
        let end_pos = pos + s.len();
        if end_pos <= data.len() {
            data[pos..end_pos].copy_from_slice(s);
        }
        self.data = data;
        self.seek(original_pos as u64);
    }

    pub fn read(&mut self, pch: &mut [u8]) -> Result<&mut Self, Error> {
        let n_size = pch.len();
        assert!(n_size <= isize::MAX as usize, "Size must be non-negative");

        let n_read_pos_next = self.cursor + n_size;
        if n_read_pos_next > self.data.len() {
            let bytes_to_read = self.data.len() - self.cursor;
            pch[..bytes_to_read].copy_from_slice(&self.data[self.cursor..]);
            pch[bytes_to_read..].fill(0);
            return Err(Error::new(ErrorKind::UnexpectedEof, "Stream::read(): end of data"));
        } else {
            pch.copy_from_slice(&self.data[self.cursor..n_read_pos_next]);
            self.cursor = n_read_pos_next;
        }

        Ok(self)
    }

    pub fn raw_read_buf(&self, start: usize, size: usize) -> &[u8] {
        &self.data[start..start + size]
    }

    pub fn read_str(&self, start: usize, size: usize) -> Result<String, std::str::Utf8Error> {
        let results = self.raw_read_buf(start, size);
        std::str::from_utf8(results).map(|s| s.to_string())
    }

    pub fn unread_str(&self) -> &[u8] {
        &self.data[self.cursor..]
    }

    pub fn size(&self) -> usize {
        self.data.len()
    }

    pub fn empty(&self) -> bool {
        self.size() == 0
    }

    pub fn resize(&mut self, n: usize, c: u8) {
        if n > self.data.len() {
            self.data.extend(vec![c; n - self.data.len()]);
        } else {
            self.data.truncate(n);
        }
        self.seek(self.cursor as u64);
    }

    pub fn begin_index(&self) -> usize {
        self.cursor
    }

    pub fn end_index(&self) -> usize {
        self.data.len()
    }

    pub fn clear(&mut self) {
        self.data.clear();
        self.cursor = 0;
    }

    pub fn insert(&mut self, pos: usize, values: &[u8]) {
        let mut data = self.data.clone();
        let start = self.cursor + pos;
        data.splice(start..start, values.iter().cloned());
        self.data = data;
        self.seek(self.cursor as u64);
    }

    pub fn erase(&mut self, start: usize, end: Option<usize>) {
        let mut data = self.data.clone();
        let end_pos = end.unwrap_or(self.data.len()).min(self.data.len());
        if start < data.len() {
            data.drain(self.cursor + start..self.cursor + end_pos);
        }
        self.data = data;
        self.seek(self.cursor as u64);
    }

    pub fn ignore(&mut self, n_size: usize) -> &mut Self {
        if n_size == 0 {
            return self;
        }

        let new_pos = self.cursor.saturating_add(n_size);
        if new_pos >= self.data.len() {
            self.data.clear();
            self.cursor = 0;
        } else {
            self.seek(new_pos as u64);
        }

        self
    }

    pub fn compact(&mut self) {
        let remaining = self.unread_str().to_vec();
        self.seek(0);
        self.clear();
        self.write_data(&remaining);
        self.seek(0);
    }

    pub fn seek(&mut self, position: u64) {
        self.cursor = position as usize;
    }

    pub fn seek_to_end(&mut self) {
        self.cursor = self.data.len();
    }

    pub fn stream_in<T: Serialize>(&mut self, obj: &T) -> io::Result<()> {
        obj.serialize_into(self);
        Ok(())
    }

    pub fn stream_out<T: Deserialize + Serialize>(&mut self) -> Result<T, std::io::Error> {
        let obj = T::deserialize(self).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        Ok(obj)
    }
}

impl AsRef<[u8]> for Stream {
    fn as_ref(&self) -> &[u8] {
        &self.data
    }
}

impl Default for Stream {
    fn default() -> Self {
        Stream {
            data: Vec::new(),
            cursor: 0,
        }
    }
}

impl Add for Stream {
    type Output = Stream;

    fn add(self, other: Stream) -> Stream {
        let mut new_data = self.data;
        new_data.extend_from_slice(&other.data);
        Stream::new(new_data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    
    

    #[test]
    fn test_stream_in_stream_out() {
        let mut stream = Stream::default();
        let a: i32 = 1;
        let b: u32 = 1000000;
        let c: String = "hello".to_string();
        let mut d: Vec<i32> = Vec::new();
        d.push(a);
        d.push(2);

        stream.stream_in(&a).unwrap();
        stream.stream_in(&b).unwrap();
        stream.stream_in(&c).unwrap();
        stream.stream_in(&d).unwrap();

        let o_a = stream.stream_out::<i32>().unwrap();
        let o_b = stream.stream_out::<u32>().unwrap();
        let o_c = stream.stream_out::<String>().unwrap();
        let o_d = stream.stream_out::<Vec<i32>>().unwrap();

        assert_eq!(o_a, a, "Expected o_a to be {}", a);
        assert_eq!(o_b, b, "Expected o_b to be {}", b);
        assert_eq!(o_c, c, "Expected o_c to be {}", c);
        assert_eq!(o_d, d, "Expected o_d to be {:?}", d);
    }
}