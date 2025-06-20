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



// A generic Bitfield struct that stores a fixed number of bits (N)
#[derive(Debug, PartialEq)]
pub struct Bitfield<const N: usize> {
    pub bits: Vec<u8>,
    pub num_bits: usize,
}

impl<const N: usize> Bitfield<N> {
    // A a new Bitfield with all bits initialized to 0
    pub fn new() -> Self {
        Bitfield {
            bits: vec![0u8; (N + 7) / 8],
            num_bits: N,
        }
    }

    pub fn set(&mut self, index: usize, value: bool) {
        // Bounds check
        if index >= self.num_bits {
            panic!("Index {} out of bounds for Bitfield<{}>", index, self.num_bits);
        }

        // Calculate the byte and bit positions
        let byte = index / 8;
        let bit = index % 8;

        if value {
            // Set the bit via bitwise OR
            self.bits[byte] |= 1 << bit;
        } else {
            // Clear the bit via bitwise AND with the neg bit mask
            self.bits[byte] &= !(1 << bit);
        }
    }

    pub fn get(&self, index: usize) -> bool {
        // Check if the index is within bounds
        if index >= self.num_bits {
            panic!("Index {} out of bounds for Bitfield<{}>", index, self.num_bits);
        }

        // Calculate the byte and bit positions
        let byte = index / 8;
        let bit = index % 8;

        // Use bitwise AND and check if the result is non-zero
        (self.bits[byte] & (1 << bit)) != 0
    }

    // Counter of 1's
    pub fn count_ones(&self) -> usize {
        let mut count = 0;

        for i in 0..self.num_bits {
            if self.get(i) {
                count += 1;
            }
        }

        count
    }
}


#[cfg(test)]
mod tests {
    use crate::bitfield::Bitfield;
    
    fn bitfield_test() {
        // Create a Bitfield with 3 bits, all initialized to false (0)
        let mut flags = Bitfield::<3>::new();

        // Set specific bits:
        flags.set(0, true);   // Set bit 0 to true (1)
        flags.set(2, true);   // Set bit 2 to true (1)

        // Verify 
        assert_eq!(flags.get(0), true);   
        assert_eq!(flags.get(1), false);  
        assert_eq!(flags.get(2), true);  

        // Check that the number of bits set to true (1s) is exactly 2
        assert_eq!(flags.count_ones(), 2);
    }
}