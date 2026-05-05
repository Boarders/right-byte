import RightByte.Mem.Prog
import RightByte.Mem.Symbolic
import RightByte.Mem.Combinators

namespace RightByte.Examples

/-- ASCII lookup table: nibble i → ASCII character.
    Indices 0-9 → '0'-'9' (0x30-0x39), indices 10-15 → 'a'-'f' (0x61-0x66). -/
def hexLUT : Vec128 :=
  ⟨#[0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
     0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66], by simp⟩

/-- SIMD base-16 encoder: reads 16 bytes at `src`, writes 32 hex-ASCII bytes to `dst`.

    The algorithm we use:
      1. Split each byte into high nibble (bits [7:4]) and low nibble (bits [3:0]).
         High nibbles: `shr16(x, 4) & 0x0F`  (16-bit lane shift then byte mask)
         Low nibbles:  `x & 0x0F`
      2. Map both nibble vectors through the ASCII lookup table via `pshufb`.
      3. Interleave: `unpacklo8(hi_ascii, lo_ascii)` and `unpackhi8(...)`.
      4. Store the two resulting 16-byte vectors (= 32 ASCII bytes total).
 -/
def base16Encode16 {var : ProgTy → Type} [Symbolic var]
    (src dst : var .nat) : Prog var Unit := do
  -- Load 16 input bytes as a SIMD register
  let input   ← Prog.effect (.vload src)
  -- Constant vectors
  let mask0f  ← Prog.effect (.vconst (Vector.replicate 16 (0x0F : UInt8)))
  let lut     ← Prog.effect (.vconst hexLUT)
  -- Low nibbles: input & 0x0F
  let lo      := Symbolic.vecOp .and128 ⟨#[input, mask0f], by simp⟩
  -- High nibbles: (input >> 4) & 0x0F
  let shifted := Symbolic.vecOp (.shr16_128 4) ⟨#[input], by simp⟩
  let hi      := Symbolic.vecOp .and128 ⟨#[shifted, mask0f], by simp⟩
  -- ASCII lookup via pshufb
  let hiAsc   := Symbolic.vecOp .shuffle128 ⟨#[lut, hi], by simp⟩
  let loAsc   := Symbolic.vecOp .shuffle128 ⟨#[lut, lo], by simp⟩
  -- Interleave: bytes 0..7  →  hiAsc[0], loAsc[0], hiAsc[1], loAsc[1], ...
  --             bytes 8..15 →  hiAsc[8], loAsc[8], ...
  let outLo   := Symbolic.vecOp .unpacklo8 ⟨#[hiAsc, loAsc], by simp⟩
  let outHi   := Symbolic.vecOp .unpackhi8 ⟨#[hiAsc, loAsc], by simp⟩
  -- Store 32 ASCII bytes
  Prog.effect (.vstore dst                                          outLo)
  Prog.effect (.vstore (Symbolic.addNat dst (Symbolic.litNat 16))  outHi)

/-- Encode an entire buffer, 16 bytes at a time.
    `nChunks` is the number of complete 16-byte input chunks.
    Reads `nChunks × 16` bytes from `src`, writes `nChunks × 32` ASCII bytes to `dst`.  -/
def base16EncodeBuffer {var : ProgTy → Type} [Symbolic var]
    (src dst nChunks : var .nat) : Prog var Unit :=
  Prog.forVarN nChunks fun i =>
    -- chunk i: src + i*16 → dst + i*32  (multiply by shifting: i<<4, i<<5)
    base16Encode16
      (Symbolic.addNat src (Symbolic.shlNat i (Symbolic.litNat 4)))
      (Symbolic.addNat dst (Symbolic.shlNat i (Symbolic.litNat 5)))

/-- Scalar nibble-to-ASCII: n → n + 48 + (n / 10) * 39.
    Gives '0'-'9' for 0-9, 'a'-'f' for 10-15. -/
def toAscii {var : ProgTy → Type} [Symbolic var] (n : var .nat) : var .nat :=
  Symbolic.addNat
    (Symbolic.addNat n (Symbolic.litNat 48))
    (Symbolic.mulNat (Symbolic.divNat n (Symbolic.litNat 10)) (Symbolic.litNat 39))

/-- Full base-16 encoder:
    Uses `Prog.chunked` to process complete 16-byte chunks via SIMD, then
    encodes the remaining 0–15 bytes scalar one-by-one. -/
def base16EncodeAll {var : ProgTy → Type} [Symbolic var]
    (src dst len : var .nat) : Prog var Unit :=
  Prog.chunked src dst len 16 32
    base16Encode16
    (fun srcTail dstTail leftover =>
      Prog.forVarN leftover fun i => do
        let byte   ← Prog.effect (.peekU8 (Symbolic.addNat srcTail i))
        let w      := Symbolic.u8ToNat byte
        let hi     := Symbolic.shrNat w (Symbolic.litNat 4)
        let lo     := Symbolic.andNat w (Symbolic.litNat 0xF)
        let dstOff := Symbolic.addNat dstTail (Symbolic.mulNat i (Symbolic.litNat 2))
        Prog.effect (.pokeU8 dstOff (Symbolic.natToU8 (toAscii hi)))
        Prog.effect (.pokeU8 (Symbolic.addNat dstOff (Symbolic.litNat 1))
                             (Symbolic.natToU8 (toAscii lo))))

end RightByte.Examples
