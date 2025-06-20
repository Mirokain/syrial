# Syrial 🧬

***Syrial*** design, with its reusable byte-level Stream buffer and compact binary encoding, might remind you the efficient serialization approach in projects like Bitcoin. It tries to offer precise control over byte manipulation, which could be helpful for protocol implementations, message parsing, storage, and other low-level data tasks.
- A flexible and reusable Stream buffer that helps with efficient byte-level input and output.
- `Serialize` and `Deserialize` traits supporting primitives, collections, arrays, tuples, enums, option, hashmap and structs  
- Compact variable-length integer encoding optimized for storage efficiency  
- Procedural macros for automatic serialization logic generation  
- Licensed under MIT.   

---

## ✨ Install 
```toml
[dependencies]
syrial = "0.2.0"
syrial-derive = "0.1.0"
```

## 🚀 Key Features

### Stream API

- **Unified Buffer**  
  A single, in-memory byte buffer enabling reading, writing, seeking, and dynamic modification.  

- **Intuitive Methods**  
  - `stream_in(&value)`: Serialize a value into the buffer  
  - `stream_out::<T>()`: Deserialize a value of type `T` from the buffer  

#### What is `Stream`?

`Stream` is a cursor-based byte buffer that extends `Vec<u8>`, providing efficient manipulation of binary data. It supports seeking, inserting, erasing, and inspecting contents while maintaining a read/write cursor position.

#### Buffer Utilities

| Method                        | Description                                                        |
|-------------------------------|--------------------------------------------------------------------|
| `write(&[u8])`                | Append raw bytes to the buffer                                     |
| `write_str(&str)`             | Append UTF-8 string bytes                                          |
| `read(&mut [u8])`             | Read bytes into a provided buffer                                 |
| `seek(pos: usize)`            | Move the cursor to an absolute position                           |
| `seek_to_end()`               | Move cursor to the buffer’s end                                   |
| `resize(n: usize, fill_byte)` | Resize buffer, truncating or filling with `fill_byte`            |
| `insert(pos: usize, &[u8])`   | Insert bytes at a specific index                                  |
| `erase(start: usize, end)`    | Remove bytes in a range `[start, end)`                           |
| `clear()`                    | Clear the buffer and reset cursor                                |
| `compact()`                  | Remove bytes before cursor to reclaim space                      |
| `to_string()`                | Convert buffer to UTF-8 string (if valid)                        |
| `find_str(&str)`             | Find substring in buffer contents                                |
| `unread_str(&str)`           | Check for substring before current cursor                        |

---

### 📝 Basic Writing and Reading Bytes

```rust
let mut s = Stream::default();

// Write raw bytes
s.write(b"Rust");
assert_eq!(s.to_string(), "Rust");

// Read bytes into a buffer
let mut buf = [0u8; 2];
s.read(&mut buf).unwrap();
assert_eq!(&buf, b"Ru");

// Cursor moves forward after read
assert_eq!(s.cursor, 2);
}

```


### ✍️ Inserting and Erasing Bytes

``` rust
let mut s = Stream::default();
s.write_str("Hello");

// Insert '!' at position 2 (after "He")
s.insert(2, b"!");
assert_eq!(s.to_string(), "He!llo");

// Erase the '!' character (position 2)
s.erase(2, Some(3));
assert_eq!(s.to_string(), "Hello");
```
### 🔄 Seeking and Resizing
``` rust
let mut s = Stream::default();
s.write_str("Hello");

// Move cursor to index 1 ('e')
s.seek(1);
assert_eq!(s.cursor, 1);

// Resize buffer to 3 bytes, truncating
s.resize(3, 0);

// Reset cursor before checking full string
s.seek(0);
assert_eq!(s.to_string(), "Hel");

// Resize buffer to 6 bytes, filling with '-'
s.resize(6, b'-');
s.seek(0);
assert_eq!(s.data, b"Hel---");
```
### 🧹 Clearing and Compacting the Stream
``` rust
let mut s = Stream::default();
s.write_str("Hello World");

// Seek to 6 ('W')
s.seek(6);

// Compact removes already-read bytes before cursor
s.compact();
assert_eq!(s.to_string(), "World");

// Clear resets buffer and cursor
s.clear();
assert!(s.empty());
assert_eq!(s.cursor, 0);
```

### ⚙️ Using stream_in and stream_out with Custom Types
``` rust
#[derive(Debug, PartialEq, Serialize, Deserialize)]
struct Point {
    x: i32,
    y: i32,
}

let mut s = Stream::default();
let p = Point { x: 10, y: -5 };

// Serialize Point into stream
s.stream_in(&p)?;

// Deserialize Point from stream
let p2: Point = s.stream_out()?;

assert_eq!(p, p2);
```

### ➕ Combining Streams with Addition
``` rust
let mut s1 = Stream::default();
s1.write_str("Hello, ");

let mut s2 = Stream::default();
s2.write_str("World!");

let s3 = s1 + s2;
assert_eq!(s3.to_string(), "Hello, World!");
```


# Serialization Traits

- **Flexible and Extensible**  
  Implement `Serialize` and `Deserialize` traits manually or derive them automatically using macros.

- **Supported Types**  
  - **Primitives**: `u8`, `i8`, `u16`, `i16`, `u32`, `i32`, `u64`, `i64`, `bool`  
  - **Collections**: `String`, `Vec<T>` where `T: Serialize + Deserialize`  
  - **Tuples**: Single and two-element tuples `(T,)`, `(K, V)`  
  - **Arrays**: Fixed-size arrays such as `[u8; 4]`, `[u8; 8]`, `[u8; 12]`, `[u8; 16]`, `[u8; 32]`, `[u8; 64]`, `[u8; 128]`  
  - **Unit Type**: `()` (zero-byte placeholder)  
  - **Custom Types**: Structs and unit enums via `#[derive(Serialize, Deserialize)]`  

---

### Compact Integer Encoding

Syrial uses a variable-length integer encoding scheme to minimize the byte footprint for smaller values, optimizing storage and transmission size.

---

### Procedural Macros

Leverage Rust’s procedural macros for auto-generating serialization and deserialization implementations:
```rust
#[derive(Serialize, Deserialize)]
struct MyType {
    // fields
}

```

✨ Quickstart Example
```rust
use syrial::stream::Stream;
use syrial::serialize::{Serialize, Deserialize};
use syrial_derive::{Serialize, Deserialize};
use syrial::serialize::SerializationError;
use syrial::stream;
use syrial::serialize;


#[derive(Debug, PartialEq, Serialize, Deserialize)]
struct CustomStruct {
    id:    u32,
    name:  String,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
enum CustomEnum {
    Foo,
    Bar,
}
fn main() -> syrial::serialize::Result<()> {
    let mut buf = Stream::default();

    // Primitives
    buf.stream_in(&123u8)?;
    buf.stream_in(&true)?;

    // Collection
    let list = vec![10u16, 20, 30];
    buf.stream_in(&list)?;

    // Custom types
    let item = CustomStruct { id: 42, name: "Alice".into() };
    buf.stream_in(&item)?;
    buf.stream_in(&CustomEnum::Bar)?;

    assert_eq!(buf.stream_out::<u8>()?, 123);
    assert_eq!(buf.stream_out::<bool>()?, true);
    assert_eq!(buf.stream_out::<Vec<u16>>()?, list);
    assert_eq!(buf.stream_out::<CustomStruct>()?, item);
    assert_eq!(buf.stream_out::<CustomEnum>()?, CustomEnum::Bar);

    println!("Done!");
    Ok(())
}

```
## Detailed Examples

Primitives & Booleans
``` rust 
let mut s = Stream::default();
// Insert values in sequence: u8, i8, u16, bool
s.stream_in(&0xFFu8)?;
s.stream_in(&-1i8)?;
s.stream_in(&65535u16)?;
s.stream_in(&true)?;

// Read back in the same order
assert_eq!(s.stream_out::<u8>()?, 0xFF);
assert_eq!(s.stream_out::<i8>()?, -1);
assert_eq!(s.stream_out::<u16>()?, 65535);
assert_eq!(s.stream_out::<bool>()?, true);

```
### Strings & Vectors

```rust
let mut s = Stream::default();
let text    = "Hello, Syrial!".to_string();
let numbers = vec![1u32, 2, 3, 4];

// Serialize
s.stream_in(&text)?;
s.stream_in(&numbers)?;

// Deserialize and verify
let deser_text: String = s.stream_out()?;
let deser_numbers: Vec<u32> = s.stream_out()?;
assert_eq!(deser_text, text);
assert_eq!(deser_numbers, numbers);
```

### Fixed‑Size Arrays

```rust
let mut s = Stream::default();
let arr4  = [1u8, 2, 3, 4];
let arr32 = [0xAAu8; 32];

// Serialize
s.stream_in(&arr4)?;
s.stream_in(&arr32)?;

// Deserialize and verify
let deser_arr4: [u8; 4] = s.stream_out()?;
let deser_arr32: [u8; 32] = s.stream_out()?;
assert_eq!(deser_arr4, arr4);
assert_eq!(deser_arr32, arr32);
```


### Option

```rust
let mut s = Stream::default();
let val_none: Option<u32> = None;
let val_some: Option<u32> = Some(12345);

// Serialize
s.stream_in(&val_none)?;
s.stream_in(&val_some)?;

// Deserialize and verify
let deser_none: Option<u32> = s.stream_out()?;
let deser_some: Option<u32> = s.stream_out()?;
assert_eq!(deser_none, val_none);
assert_eq!(deser_some, val_some);
```


### HashMap

```rust
let mut s = Stream::default();
let mut map = HashMap::new();
map.insert(1u8, String::from("one"));
map.insert(2u8, String::from("two"));

// Serialize
s.stream_in(&map)?;

// Deserialize and verify
let deser_map: HashMap<u8, String> = s.stream_out()?;
assert_eq!(deser_map, map);
```


### Custom Types

```rust
use syrial_derive::{Serialize, Deserialize};

#[derive(Debug, PartialEq, Serialize, Deserialize)]
struct Point {
    x: i32,
    y: i32,
}

let mut s = Stream::default();
let p = Point { x: 5, y: -7 };

// Serialize using derived impl
s.stream_in(&p)?;

// Deserialize and verify
let p2: Point = s.stream_out()?;
assert_eq!(p2, p);
```
