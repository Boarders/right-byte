import RightByte.Mem.Prog
import RightByte.C.AST

namespace RightByte

/-- Fresh name monad: generates unique variable names. -/
abbrev FreshM := StateM Nat

def FreshM.fresh (pfx : String := "v") : FreshM String := do
  let n ← get
  set (n + 1)
  pure s!"{pfx}{n}"

/-- Compile a single memory effect to statements plus a result expression.
    Read ops return the `CExpr` that represents the loaded value (= `var τ`
    with `var = fun _ => CExpr`); write ops return `Unit`. -/
private def compileMemOp {α : Type} : MemOp (fun _ => CExpr) α → FreshM (List CStmt × α)
  | .peekU8    addr   => pure ([], .scalarLoad .u8  addr)
  | .peekU32le addr   => pure ([], .scalarLoad .u32 addr)
  | .pokeU8    addr v => pure ([.assign (.scalarLoad .u8  addr) v], ())
  | .pokeU32le addr v => pure ([.assign (.scalarLoad .u32 addr) v], ())
  | .vload     addr   => pure ([], .vecLoad .unaligned (.cast (.ptr .vec128) addr))
  | .vloadA    addr   => pure ([], .vecLoad .aligned   (.cast (.ptr .vec128) addr))
  | .vstore    addr v => pure ([.vecStore .unaligned (.cast (.ptr .vec128) addr) v], ())
  | .vstoreA   addr v => pure ([.vecStore .aligned   (.cast (.ptr .vec128) addr) v], ())
  | .vconst    v      => do
      let name ← FreshM.fresh "vc"
      pure ([.decl .vec128 name (.vecConst v)], .var name)

/-- Walk a symbolic program, threading fresh names through each `letIn` step. -/
private def goStep {α : Type} : Prog (fun _ => CExpr) α → FreshM (List CStmt × α)
  | .pure a => pure ([], a)
  | .letIn m f => do
      let (stmts1, a) ← goStep m
      let (stmts2, b) ← goStep (f a)
      pure (stmts1 ++ stmts2, b)
  | .effect op => compileMemOp op
  | .forN n body => do
      let idx ← FreshM.fresh "i"
      let (bodyStmts, _) ← goStep (body (.var idx))
      let loop := .forN idx (.lit n.toUInt64) (.block bodyStmts)
      pure ([loop], ())
  | .forVarN n body => do
      let idx ← FreshM.fresh "i"
      let (bodyStmts, _) ← goStep (body (.var idx))
      let loop := .forN idx n (.block bodyStmts)
      pure ([loop], ())
  | .ifElse cond t e => do
      let (tStmts, r) ← goStep t
      let (eStmts, _) ← goStep e
      pure ([.ifElse cond (.block tStmts) (.block eStmts)], r)
  | .abort msg =>
      -- The CStmt.abort ensures the C runtime never reaches the continuation,
      -- so the `sorry` value is dead code and never observed.
      pure ([.abort msg], sorry)
  | .select cond t e => pure ([], .ternary cond t e)

/-- Compile a unit-returning symbolic program to a list of C statements. -/
def compile (p : Prog (fun _ => CExpr) Unit) : FreshM (List CStmt) :=
  Prod.fst <$> goStep p

end RightByte
