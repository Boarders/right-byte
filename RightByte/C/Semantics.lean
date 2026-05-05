import RightByte.C.AST
import Mathlib.Data.Finmap

namespace RightByte

/-- Runtime values in the C semantics. -/
inductive CVal where
  | u8    : UInt8  → CVal
  | u16   : UInt16 → CVal
  | u32   : UInt32 → CVal
  | u64   : UInt64 → CVal
  | vec128: Vec128 → CVal

/-- C environment: maps variable names to runtime values. -/
abbrev CEnv := Finmap (fun _ : String => CVal)

/-- Collect `n` Vec128 values from a fallible `Fin n → Option CVal`, building a `Vector`. -/
private def collectVec128 : {n : Nat} → (Fin n → Option CVal) → Option (Vector Vec128 n)
  | 0,   _ => some ⟨#[], rfl⟩
  | n+1, f => do
      let v  ← collectVec128 (fun i => f i.castSucc)
      let cv ← f ⟨n, Nat.lt_succ_self n⟩
      match cv with
      | .vec128 x => some (v.push x)
      | _         => none

def CExpr.eval (env : CEnv) : CExpr → Option CVal
  | .lit n    => some (.u64 n)
  | .var x    => env.lookup x
  | .cast _ e => e.eval env   -- truncation/extension not modelled here
  | .binop op e1 e2 =>
      match e1.eval env, e2.eval env with
      | some (.u8  a), some (.u8  b) =>
          some (.u8  (match op with
            | .add => a+b | .sub => a-b | .mul => a*b | .div => a/b | .mod => a%b
            | .xor => a^^^b | .and => a&&&b | .or => a|||b
            | .shl => a<<<b | .shr => a>>>b))
      | some (.u16 a), some (.u16 b) =>
          some (.u16 (match op with
            | .add => a+b | .sub => a-b | .mul => a*b | .div => a/b | .mod => a%b
            | .xor => a^^^b | .and => a&&&b | .or => a|||b
            | .shl => a<<<b | .shr => a>>>b))
      | some (.u32 a), some (.u32 b) =>
          some (.u32 (match op with
            | .add => a+b | .sub => a-b | .mul => a*b | .div => a/b | .mod => a%b
            | .xor => a^^^b | .and => a&&&b | .or => a|||b
            | .shl => a<<<b | .shr => a>>>b))
      | some (.u64 a), some (.u64 b) =>
          some (.u64 (match op with
            | .add => a+b | .sub => a-b | .mul => a*b | .div => a/b | .mod => a%b
            | .xor => a^^^b | .and => a&&&b | .or => a|||b
            | .shl => a<<<b | .shr => a>>>b))
      | _, _ => none
  | .shl e n  =>
      match e.eval env with
      | some (.u64 v) => some (.u64 (v <<< n.toUInt64))
      | _ => none
  | .shr e n  =>
      match e.eval env with
      | some (.u64 v) => some (.u64 (v >>> n.toUInt64))
      | _ => none
  | .vecOp op args =>
      match collectVec128 (fun i => (args i).eval env) with
      | some vs => some (.vec128 (op.scalarSem vs))
      | none    => none
  | .vecLoad _ _    => none   -- heap not modelled in CExpr.eval
  | .scalarLoad _ _ => none   -- heap not modelled in CExpr.eval
  | .vecConst v     => some (.vec128 v)

/-- Execute a C statement, updating the environment. -/
def CSemantics.exec (env : CEnv) : CStmt → CEnv
  | .decl _ name expr =>
      match expr.eval env with
      | some val => env.insert name val
      | none     => env
  | .assign (.var x) expr =>
      match expr.eval env with
      | some val => env.insert x val
      | none     => env
  | .assign _ _     => env  -- non-variable lhs not modelled
  | .vecStore _ _ _ => env  -- stores affect heap, not C env; modelled separately
  | .vecReduce op name expr =>
      match expr.eval env with
      | some (.vec128 v) =>
          let val := match op with
            | .movemask   => CVal.u16 (VecReduceOp.scalarSem .movemask v)
            | .testz      => CVal.u32 (if VecReduceOp.scalarSem .testz v then 1 else 0)
            | .extract8 i => CVal.u8  (VecReduceOp.scalarSem (.extract8 i) v)
          env.insert name val
      | _ => env
  | .forN idx bound body =>
      match bound.eval env with
      | some (.u64 n) =>
          (List.range n.toNat).foldl (fun env' i =>
            CSemantics.exec (env'.insert idx (.u64 i.toUInt64)) body) env
      | _ => env
  | .ifElse cond t e =>
      match cond.eval env with
      | some (.u8 0) | some (.u16 0) | some (.u32 0) | some (.u64 0) => CSemantics.exec env e
      | some (.u8 _) | some (.u16 _) | some (.u32 _) | some (.u64 _) => CSemantics.exec env t
      | _ => env
  | .block stmts => stmts.foldl CSemantics.exec env
  | .abort _    => env  -- unreachable in well-formed programs

end RightByte
