# scroll-buffer
Additional `Pwrite` buffers for use with [Scroll](https://github.com/m4b/scroll).

## Overview
Since Scroll's writing traits are generic over their destination buffer, if you find
the default mutable byte slice too restrictive, you can use the types in this crate
for more powerful features like dynamic allocation.

Currently, this crate only defines one such buffer: the `DynamicBuffer` type, which
grows on-demand when writing types into it.

## Usage
Add to your `Cargo.toml`:
```toml
[dependencies]
scroll-buffer = "0.1.0"
```

You can now change your `TryIntoCtx` implementations and start writing!

```rust
use scroll::{LE, Pwrite, ctx::TryIntoCtx};
use scroll_buffer::DynamicBuffer;

fn main() -> Result<(), scroll::Error> {
    let mut buf = DynamicBuffer::new();
    
    // works with regular ints, of course...
    buf.pwrite_with(0xbeefu16, 0, LE)?;
    assert_eq!(buf.get(), [0xef, 0xbe]);
    
    // ...but also custom types!
    struct MyCoolStruct(bool, u32);
    impl TryIntoCtx<(), DynamicBuffer> for MyCoolStruct {
        type Error = scroll::Error;

        fn try_into_ctx(self, buf: &mut DynamicBuffer, _: ()) -> Result<usize, Self::Error> {
            let offset = &mut 0;
            
            if self.0 {
                buf.gwrite_with(0xffu8, offset, LE)?;
            } else {
                buf.gwrite_with(self.1, offset, LE)?;
            }
            
            Ok(*offset)
        }
    }
    
    buf.clear();
    buf.pwrite(MyCoolStruct(false, 1), 0)?;
    assert_eq!(buf.get(), [0x01, 0x00, 0x00, 0x00]);
    
    buf.pwrite(MyCoolStruct(true, 0), 4)?;
    assert_eq!(buf.get(), [0x01, 0x00, 0x00, 0x00, 0xff]);
    
    Ok(())
}
```
