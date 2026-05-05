import RightByte.C.AST

namespace RightByte

/-- Target architecture: maps abstract SIMD ops to concrete intrinsic names. -/
structure Arch where
  opName     : ∀ {n}, VecOp n → String
  loadName   : VecMemOp → String
  storeName  : VecMemOp → String
  reduceName : VecReduceOp → String
  simdHeader : String

def x86 : Arch where
  opName := fun op => match op with
    | .xor128     => "_mm_xor_si128"
    | .and128     => "_mm_and_si128"
    | .or128      => "_mm_or_si128"
    | .add8_128   => "_mm_add_epi8"
    | .shuffle128 => "_mm_shuffle_epi8"
    | .broadcast8 => "_mm_set1_epi8"
    | .blend128   => "_mm_blendv_epi8"
    | .shl16_128 _ => "_mm_slli_epi16"
    | .shr16_128 _ => "_mm_srli_epi16"
    | .shl32_128 _ => "_mm_slli_epi32"
    | .shr32_128 _ => "_mm_srli_epi32"
    | .unpacklo8   => "_mm_unpacklo_epi8"
    | .unpackhi8   => "_mm_unpackhi_epi8"
    | .cmpgt8_128  => "_mm_cmpgt_epi8"
  loadName := fun memOp => match memOp with
    | .unaligned => "_mm_loadu_si128"
    | .aligned   => "_mm_load_si128"
  storeName := fun memOp => match memOp with
    | .unaligned => "_mm_storeu_si128"
    | .aligned   => "_mm_store_si128"
  reduceName := fun op => match op with
    | .movemask   => "_mm_movemask_epi8"
    | .testz      => "_mm_testz_si128"
    | .extract8 _ => "_mm_extract_epi8"

  simdHeader := "#include <immintrin.h>"

def arm : Arch where
  opName := fun op => match op with
    | .xor128     => "veorq_u8"
    | .and128     => "vandq_u8"
    | .or128      => "vorrq_u8"
    | .add8_128   => "vaddq_u8"
    | .shuffle128 => "vqtbl1q_u8"
    | .broadcast8 => "vdupq_n_u8"
    | .blend128   => "vbslq_u8"
    | .shl16_128 _ => "vshlq_n_u16"
    | .shr16_128 _ => "vshrq_n_u16"
    | .shl32_128 _ => "vshlq_n_u32"
    | .shr32_128 _ => "vshrq_n_u32"
    | .unpacklo8   => "vzip1q_u8"
    | .unpackhi8   => "vzip2q_u8"
    | .cmpgt8_128  => "vcgtq_s8"
  loadName  := fun _ => "vld1q_u8"   -- ARM doesn't distinguish aligned/unaligned
  storeName := fun _ => "vst1q_u8"
  reduceName := fun op => match op with
    | .movemask   => "arm_movemask"
    | .testz      => "arm_testz"
    | .extract8 _ => "vgetq_lane_u8"
  simdHeader := "#include <arm_neon.h>"

end RightByte
