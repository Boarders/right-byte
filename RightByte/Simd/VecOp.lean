import RightByte.Simd.Vec

namespace RightByte

/-- SIMD operations, indexed by arity (number of Vec128 inputs). -/
inductive VecOp : Nat → Type where
  | xor128     : VecOp 2
  | and128     : VecOp 2
  | or128      : VecOp 2
  | add8_128   : VecOp 2
  /-- pshufb: args[0] = data, args[1] = mask.
      output[i] = 0 if mask[i] &&& 0x80 ≠ 0, else data[mask[i] &&& 0x0F] -/
  | shuffle128 : VecOp 2
  /-- Broadcast the first byte of the input to all 16 lanes. -/
  | broadcast8 : VecOp 1
  /-- Byte-granularity blend: select b[i] if mask[i] &&& 0x80 ≠ 0, else a[i]. -/
  | blend128   : VecOp 3
  /-- Shift each 16-bit lane left by a compile-time constant. (`_mm_slli_epi16`) -/
  | shl16_128  : Nat → VecOp 1
  /-- Logical right shift of each 16-bit lane by a compile-time constant. (`_mm_srli_epi16`) -/
  | shr16_128  : Nat → VecOp 1
  /-- Shift each 32-bit lane left by a compile-time constant. (`_mm_slli_epi32`) -/
  | shl32_128  : Nat → VecOp 1
  /-- Logical right shift of each 32-bit lane by a compile-time constant. (`_mm_srli_epi32`) -/
  | shr32_128  : Nat → VecOp 1
  /-- Interleave low 8 bytes of two vectors. (`_mm_unpacklo_epi8`) -/
  | unpacklo8  : VecOp 2
  /-- Interleave high 8 bytes of two vectors. (`_mm_unpackhi_epi8`) -/
  | unpackhi8  : VecOp 2
  /-- Signed byte compare greater-than: output[i] = 0xFF if a[i] > b[i] (signed), else 0x00.
      (`_mm_cmpgt_epi8` / `vcgtq_s8`) -/
  | cmpgt8_128 : VecOp 2

/-- Returns the compile-time immediate for ops that require one (e.g. shift amounts). -/
def VecOp.immediate : VecOp n → Option Nat
  | .shl16_128 n | .shr16_128 n | .shl32_128 n | .shr32_128 n => some n
  | _ => none

/-- Tag for SIMD reductions.  Lives in `Type` (no universe bump) because the
    result type is given by the separate `VecReduceOp.Ty` type family. -/
inductive VecReduceOp where
  | movemask
  | testz
  | extract8 : Fin 16 → VecReduceOp

/-- The Lean type produced by each reduction. -/
@[reducible] def VecReduceOp.Ty : VecReduceOp → Type
  | .movemask   => UInt16
  | .testz      => Bool
  | .extract8 _ => UInt8

def applyLane16 (f : UInt16 → UInt16) (v : Vec128) : Vec128 :=
  Vector.ofFn fun i : Fin 16 =>
    have h0 : i.val / 2 * 2     < 16 := by omega
    have h1 : i.val / 2 * 2 + 1 < 16 := by omega
    let lo  := v.get ⟨i.val / 2 * 2,     h0⟩ |>.toUInt16
    let hi  := v.get ⟨i.val / 2 * 2 + 1, h1⟩ |>.toUInt16
    let out := f (hi <<< (8 : UInt16) ||| lo)
    if i.val % 2 == 0 then out.toUInt8 else (out >>> (8 : UInt16)).toUInt8

/-- Element at an even index 2k: low byte of the 16-bit lane operation. -/
theorem applyLane16_even (f : UInt16 → UInt16) (v : Vec128) (k : Fin 8) :
    (applyLane16 f v).get ⟨k.val * 2, by omega⟩ =
    let lo := (v.get ⟨k.val * 2,     by omega⟩).toUInt16
    let hi := (v.get ⟨k.val * 2 + 1, by omega⟩).toUInt16
    (f (hi <<< (8 : UInt16) ||| lo)).toUInt8 := by
  simp only [applyLane16, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn, Fin.val_cast]
  have hdiv : k.val * 2 / 2 = k.val := by omega
  have hmod : k.val * 2 % 2 = 0 := by omega
  simp only [hdiv, hmod, beq_self_eq_true, ↓reduceIte]

/-- Element at an odd index 2k+1: high byte of the 16-bit lane operation. -/
theorem applyLane16_odd (f : UInt16 → UInt16) (v : Vec128) (k : Fin 8) :
    (applyLane16 f v).get ⟨k.val * 2 + 1, by omega⟩ =
    let lo := (v.get ⟨k.val * 2,     by omega⟩).toUInt16
    let hi := (v.get ⟨k.val * 2 + 1, by omega⟩).toUInt16
    ((f (hi <<< (8 : UInt16) ||| lo)) >>> (8 : UInt16)).toUInt8 := by
  simp only [applyLane16, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn, Fin.val_cast]
  have hdiv : (k.val * 2 + 1) / 2 = k.val := by omega
  have hmod : (k.val * 2 + 1) % 2 = 1 := by omega
  simp only [hdiv, hmod, show (1 : Nat) == (0 : Nat) ↔ False from by decide, ↓reduceIte]

private def applyLane32 (f : UInt32 → UInt32) (v : Vec128) : Vec128 :=
  Vector.ofFn fun i : Fin 16 =>
    have h0 : i.val / 4 * 4     < 16 := by omega
    have h1 : i.val / 4 * 4 + 1 < 16 := by omega
    have h2 : i.val / 4 * 4 + 2 < 16 := by omega
    have h3 : i.val / 4 * 4 + 3 < 16 := by omega
    let b j hj := v.get ⟨i.val / 4 * 4 + j, hj⟩ |>.toUInt32
    let out := f (b 3 h3 <<< (24 : UInt32) ||| b 2 h2 <<< (16 : UInt32) ||| b 1 h1 <<< (8 : UInt32) ||| b 0 h0)
    (out >>> ((8 : UInt32) * (i.val % 4).toUInt32)).toUInt8

def VecOp.scalarSem : VecOp n → Vector Vec128 n → Vec128
  | .xor128,    args => args[0].zipWith (· ^^^ ·) args[1]
  | .and128,    args => args[0].zipWith (· &&& ·) args[1]
  | .or128,     args => args[0].zipWith (· ||| ·) args[1]
  | .add8_128,  args => args[0].zipWith (· + ·) args[1]
  | .shuffle128, args =>
      let data := args[0]
      let mask := args[1]
      Vector.ofFn (fun i =>
        if mask[i] &&& 0x80 != 0 then 0
        else data[(mask[i] &&& 0x0F).toNat]!)
  | .broadcast8, args => Vector.replicate 16 args[0][0]
  | .blend128,  args =>
      let a    := args[0]
      let b    := args[1]
      let mask := args[2]
      Vector.ofFn (fun i => if mask[i] &&& 0x80 != 0 then b[i] else a[i])
  | .shl16_128 n, args => applyLane16 (· <<< n.toUInt16) args[0]
  | .shr16_128 n, args => applyLane16 (· >>> n.toUInt16) args[0]
  | .shl32_128 n, args => applyLane32 (· <<< n.toUInt32) args[0]
  | .shr32_128 n, args => applyLane32 (· >>> n.toUInt32) args[0]
  | .unpacklo8, args =>
      -- result[2i] = a[i], result[2i+1] = b[i] for i in 0..7
      let a := args[0]; let b := args[1]
      Vector.ofFn fun (i : Fin 16) =>
        if i.val % 2 = 0 then a[i.val / 2]! else b[i.val / 2]!
  | .unpackhi8, args =>
      -- result[2i] = a[8+i], result[2i+1] = b[8+i] for i in 0..7
      let a := args[0]; let b := args[1]
      Vector.ofFn fun (i : Fin 16) =>
        if i.val % 2 = 0 then a[8 + i.val / 2]! else b[8 + i.val / 2]!
  | .cmpgt8_128, args =>
      let toSigned (x : UInt8) : Int :=
        if x.toNat < 128 then x.toNat else x.toNat - 256
      args[0].zipWith (fun a b => if toSigned a > toSigned b then 0xFF else 0x00) args[1]

def VecReduceOp.scalarSem : (op : VecReduceOp) → Vec128 → op.Ty
  | .movemask, v =>
      (List.range 16).foldl (fun (acc : UInt16) (i : Nat) =>
        if v[i]! &&& 0x80 != 0 then acc ||| ((1 : UInt16) <<< i.toUInt16) else acc) 0
  | .testz, v => v.toArray.all (· == 0)
  | .extract8 i, v => v[i]

end RightByte
