import RightByte.Expr.Basic
import RightByte.Simd.VecOp

namespace RightByte

inductive CType where
  | u8 | u16 | u32 | u64
  | vec128 | vec256
  | ptr : CType → CType

/-- Whether a vector load or store uses an aligned or unaligned intrinsic. -/
inductive VecMemOp where
  | unaligned
  | aligned

/-- C expression AST. -/
inductive CExpr where
  | lit     : UInt64 → CExpr
  | var     : String → CExpr
  | cast    : CType → CExpr → CExpr
  | binop   : BinOp → CExpr → CExpr → CExpr
  /-- Left shift by a compile-time constant. Maps to `_mm_slli_epiN` or `<<`. -/
  | shl     : CExpr → Nat → CExpr
  /-- Right (logical) shift by a compile-time constant. Maps to `_mm_srli_epiN` or `>>`. -/
  | shr     : CExpr → Nat → CExpr
  | vecOp   : {n : Nat} → VecOp n → (Fin n → CExpr) → CExpr
  | vecLoad    : VecMemOp → CExpr → CExpr          -- load Vec128 from pointer
  | scalarLoad : CType → CExpr → CExpr             -- *(T*)ptr, for scalar reads
  /-- A compile-time Vec128 constant.  Compiles to `_mm_set_epi8(...)`. -/
  | vecConst   : Vec128 → CExpr
  /-- C ternary: `cond ? t : e`. Used to compile value-returning selects. -/
  | ternary    : CExpr → CExpr → CExpr → CExpr

/-- C statement AST. -/
inductive CStmt where
  | decl      : CType → String → CExpr → CStmt
  | assign    : CExpr → CExpr → CStmt
  | vecStore  : VecMemOp → CExpr → CExpr → CStmt   -- ptr, value
  /-- Reduce a Vec128 to a scalar and bind the result to a fresh variable. -/
  | vecReduce : VecReduceOp → String → CExpr → CStmt
  | forN      : String → CExpr → CStmt → CStmt      -- var, bound, body
  | ifElse    : CExpr → CStmt → CStmt → CStmt
  | block     : List CStmt → CStmt
  /-- Unconditional abort with a diagnostic message.  Compiles to `abort()`. -/
  | abort     : String → CStmt

end RightByte
