import RightByte.Mem.MemOp

namespace RightByte

/-- An imperative program over heap memory, parameterised by `var : ProgTy → Type`.

    We use PHOAS and so:
      - Setting `var = ProgTy.Ty` gives an executable program
      - Setting `var = fun _ => CExpr` gives a symbolic program that can be
        compiled to C.

    `forN n body` is a bounded for loop, the body uses a PHOAS-style variable
    `var .nat` -- so the loop variable is available as a `CExpr` in compilation mode.
 -/
inductive Prog (var : ProgTy → Type) : Type → Type 1 where
  | pure    : α → Prog var α
  | letIn   : Prog var α → (α → Prog var β) → Prog var β
  | effect  : MemOp var α → Prog var α
  /-- Static loop: bound is a compile-time `Nat`. -/
  | forN    : Nat → (var .nat → Prog var Unit) → Prog var Unit
  /-- Dynamic loop: bound is a runtime `var .nat` (e.g. a function parameter). -/
  | forVarN : var .nat → (var .nat → Prog var Unit) → Prog var Unit
  | ifElse  : var .bool → Prog var α → Prog var α → Prog var α
  | abort   : String → Prog var α
  /-- Select between two `var .nat` values based on a runtime boolean.
      Compiles to a C ternary `cond ? t : e`. -/
  | select  : var .bool → var .nat → var .nat → Prog var (var .nat)

/-- Specialisation of `Prog` to concrete execution (`var = ProgTy.Ty`). -/
abbrev ProgExec := Prog ProgTy.Ty

instance (var : ProgTy → Type) : Monad (Prog var) where
  pure  := .pure
  bind  := .letIn

def ProgExec.exec : ProgExec α → Heap → Option (α × Heap)
  | .pure a,       h => some (a, h)
  | .letIn m f,    h =>
      match ProgExec.exec m h with
      | none => none
      | some (a, h') => ProgExec.exec (f a) h'
  | .effect op,    h => some (op.exec h)
  | .forN n body,  h =>
      match (List.range n).foldl (fun acc i =>
          match acc with
          | none => none
          | some h =>
              match ProgExec.exec (body i) h with
              | none => none
              | some (_, h') => some h') (some h) with
      | none => none
      | some h' => some ((), h')
  | .forVarN n body, h =>
      match (List.range n).foldl (fun acc i =>
          match acc with
          | none => none
          | some h =>
              match ProgExec.exec (body i) h with
              | none => none
              | some (_, h') => some h') (some h) with
      | none => none
      | some h' => some ((), h')
  | .ifElse c t e, h => if c then ProgExec.exec t h else ProgExec.exec e h
  | .abort _,      _ => none
  | .select c t e, h => some (if c then t else e, h)

-- Semantic monad laws: the laws hold on `exec`, not syntactically on `Prog`.

-- Semantic monad laws: hold definitionally for all constructors.
theorem ProgExec.exec_pure_bind (a : α) (f : α → ProgExec β) (σ : Heap) :
    ProgExec.exec (pure a >>= f) σ = ProgExec.exec (f a) σ := by
  rfl

theorem ProgExec.exec_bind_pure (m : ProgExec α) (σ : Heap) :
    ProgExec.exec (m >>= pure) σ = ProgExec.exec m σ := by
  induction m <;> simp [ProgExec.exec, pure, bind] <;> grind

theorem ProgExec.exec_bind_assoc
    (m : ProgExec α) (f : α → ProgExec β) (g : β → ProgExec γ) (σ : Heap) :
    ProgExec.exec ((m >>= f) >>= g) σ = ProgExec.exec (m >>= fun x => f x >>= g) σ := by
  induction m <;> simp [bind, ProgExec.exec] <;> grind

end RightByte
