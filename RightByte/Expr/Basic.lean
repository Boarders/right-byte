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

/-- Expression language, indexed by an `ExprTy` for the type of the term
-/
inductive Expr : ExprTy → Type where
  | litBV  : BitVec n → Expr (.bv n)
  | litU8  : UInt8 → Expr .u8
  | var    : Var (τ.Ty) → Expr τ
  | binOp  : BinOp → Expr (.bv n) → Expr (.bv n) → Expr (.bv n)
  | shiftL : Expr (.bv n) → Nat → Expr (.bv n)
  | shiftR : Expr (.bv n) → Nat → Expr (.bv n)
  /-- Extract bits [lo, hi), producing a BitVec of width hi - lo. -/
  | slice  : (lo hi : Nat) → Expr (.bv n) → Expr (.bv (hi - lo))
  /-- Concatenate: e1 in the high bits, e2 in the low bits. -/
  | concat : Expr (.bv m) → Expr (.bv n) → Expr (.bv (m + n))
  /-- Zero-extend a BitVec m to width n. -/
  | zext   : (n : Nat) → Expr (.bv m) → Expr (.bv n)
  /-- A vector operation which takes in k Vec128 inputs
      Note: We take this in the container form Fin k -> Expr .vec128 -/
  | vecOp  : VecOp k → (Fin k → Expr .vec128) → Expr .vec128

/-- Evaluate an expression under an environment. -/
def Expr.eval : Expr τ → Env → τ.Ty
  | .litBV b,        _   => b
  | .litU8 n,        _   => n
  | .var v,          env => env v
  | .binOp op e1 e2, env => op.sem (e1.eval env) (e2.eval env)
  | .shiftL e n,     env => e.eval env <<< n
  | .shiftR e n,     env => e.eval env >>> n
  | .slice lo _ e,   env => BitVec.ofNat _ ((e.eval env).toNat >>> lo)
  | .concat e1 e2,   env => e1.eval env ++ e2.eval env
  | .zext n e,       env => BitVec.ofNat n (e.eval env).toNat
  | .vecOp op args,  env => op.scalarSem (Vector.ofFn (fun i => (args i).eval env))

end RightByte
