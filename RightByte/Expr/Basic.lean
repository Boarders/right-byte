import RightByte.Simd.VecOp

namespace RightByte

/-- A typed variable. The type parameter `τ` is phantom but ensures
    that a variable can only be used at the type it was declared with. -/
structure Var (τ : Type) where
  name : String

/-- An environment maps every typed variable to a value of the appropriate type. -/
abbrev Env := ∀ {τ : Type}, Var τ → τ

/-- Symmetric binary operations on `BitVec n`: both inputs and the output share the same width. -/
inductive BinOp where
  | add | sub | mul | div | mod
  | xor | and | or
  | shl | shr
  | lt

def BinOp.sem : BinOp → BitVec n → BitVec n → BitVec n
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)
  | .mod => (· % ·)
  | .xor => (· ^^^ ·)
  | .and => (· &&& ·)
  | .or  => (· ||| ·)
  | .shl => fun a b => a <<< b.toNat
  | .shr => fun a b => a >>> b.toNat
  | .lt  => fun a b => if a.toNat < b.toNat then BitVec.allOnes n else 0

/-- The closed universe of types that `Expr` can produce. -/
inductive ExprTy where
  | bv  : Nat → ExprTy
  | u8  : ExprTy
  | vec128 : ExprTy

/-- Semantically interpret an `ExprTy` as the concrete lean type. -/
@[reducible] def ExprTy.Ty : ExprTy → Type
  | .bv n  => BitVec n
  | .u8    => UInt8
  | .vec128 => Vec128

end RightByte
