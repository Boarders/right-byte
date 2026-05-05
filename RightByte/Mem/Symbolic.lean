import RightByte.Mem.Prog
import RightByte.C.AST

namespace RightByte

/-- Typeclass abstracting primitive numeric and SIMD operations over a `var` functor.
    When `var = ProgTy.Ty` the operations are concrete Lean computations;
    when `var = fun _ => CExpr` they build C expression trees.
-/
class Symbolic (var : ProgTy → Type) where
  litNat   : Nat → var .nat
  -- Arithmetic
  addNat   : var .nat → var .nat → var .nat
  subNat   : var .nat → var .nat → var .nat
  mulNat   : var .nat → var .nat → var .nat
  divNat   : var .nat → var .nat → var .nat
  modNat   : var .nat → var .nat → var .nat
  -- Bitwise
  andNat   : var .nat → var .nat → var .nat
  orNat    : var .nat → var .nat → var .nat
  shlNat   : var .nat → var .nat → var .nat
  shrNat   : var .nat → var .nat → var .nat
  -- Comparison
  ltNat    : var .nat → var .nat → var .bool
  -- Byte ↔ nat
  u8ToNat  : var .u8 → var .nat
  natToU8  : var .nat → var .u8
  -- SIMD
  vecOp    : {k : Nat} → VecOp k → Vector (var .vec128) k → var .vec128

instance : Symbolic ProgTy.Ty where
  litNat n      := n
  addNat a b    := a + b
  subNat a b    := a - b
  mulNat a b    := a * b
  divNat a b    := a / b
  modNat a b    := a % b
  andNat a b    := a &&& b
  orNat  a b    := a ||| b
  shlNat a b    := a <<< b
  shrNat a b    := a >>> b
  ltNat  a b    := decide (a < b)
  u8ToNat b     := b.toNat
  natToU8 n     := n.toUInt8
  vecOp op args := VecOp.scalarSem op args

instance : Symbolic (fun _ => CExpr) where
  litNat n      := .lit n.toUInt64
  addNat a b    := .binop .add a b
  subNat a b    := .binop .sub a b
  mulNat a b    := .binop .mul a b
  divNat a b    := .binop .div a b
  modNat a b    := .binop .mod a b
  andNat a b    := .binop .and a b
  orNat  a b    := .binop .or  a b
  shlNat a b    := .binop .shl a b
  shrNat a b    := .binop .shr a b
  ltNat  a b    := .binop .lt  a b
  u8ToNat e     := .cast .u64 e
  natToU8 e     := .cast .u8  e
  vecOp op args := .vecOp op args.get

end RightByte
