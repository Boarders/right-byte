# right-byte

A project for writing verified byte-level protocols and programs using SIMD in `lean` which are output as `C`
programs free of certain classes of memory errors.

# example

For an example of how it currently looks, we can write a SIMD implementation of
a `base16` encoder as follows:

```lean
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
```

This then outputs the following `C` code:

```C
#include <immintrin.h>

void base16_encode(const uint8_t* src, uint8_t* dst, size_t len) {
  for (uint32_t i0 = 0; i0 < (len / 16); i0++) {
    __m128i vc1 = _mm_set_epi8(15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15);
    __m128i vc2 = _mm_set_epi8(102, 101, 100, 99, 98, 97, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48);
    _mm_storeu_si128((__m128i*)((dst + (i0 * 32))), _mm_unpacklo_epi8(_mm_shuffle_epi8(vc2, _mm_and_si128(_mm_srli_epi16(_mm_loadu_si128((__m128i*)((src + (i0 * 16)))), 4), vc1)), _mm_shuffle_epi8(vc2, _mm_and_si128(_mm_loadu_si128((__m128i*)((src + (i0 * 16)))), vc1))));
    _mm_storeu_si128((__m128i*)(((dst + (i0 * 32)) + 16)), _mm_unpackhi_epi8(_mm_shuffle_epi8(vc2, _mm_and_si128(_mm_srli_epi16(_mm_loadu_si128((__m128i*)((src + (i0 * 16)))), 4), vc1)), _mm_shuffle_epi8(vc2, _mm_and_si128(_mm_loadu_si128((__m128i*)((src + (i0 * 16)))), vc1))));
  }
  for (uint32_t i3 = 0; i3 < (len % 16); i3++) {
    *(uint8_t*)(((dst + ((len / 16) * 32)) + (i3 * 2))) = (uint8_t)(((((uint64_t)(*(uint8_t*)(((src + ((len / 16) * 16)) + i3))) >> 4) + 48) + ((((uint64_t)(*(uint8_t*)(((src + ((len / 16) * 16)) + i3))) >> 4) / 10) * 39)));
    *(uint8_t*)((((dst + ((len / 16) * 32)) + (i3 * 2)) + 1)) = (uint8_t)(((((uint64_t)(*(uint8_t*)(((src + ((len / 16) * 16)) + i3))) & 15) + 48) + ((((uint64_t)(*(uint8_t*)(((src + ((len / 16) * 16)) + i3))) & 15) / 10) * 39)));
  }
}
```
