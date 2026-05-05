import RightByte.Mem.Heap
import RightByte.Simd.Vec

namespace RightByte

/-- The closed set of types that appear as values in memory programs. -/
inductive ProgTy where
  | unit | bool | nat | u8 | u32 | vec128

/-- Interpret a `ProgTy` tag as the corresponding Lean type. -/
@[reducible] def ProgTy.Ty : ProgTy → Type
  | .unit   => Unit
  | .bool   => Bool
  | .nat    => Nat
  | .u8     => UInt8
  | .u32    => UInt32
  | .vec128 => Vec128

instance instInhabitedProgTyTy (τ : ProgTy) : Inhabited (ProgTy.Ty τ) where
  default := match τ with
    | .unit   => ()
    | .bool   => false
    | .nat    => 0
    | .u8     => 0
    | .u32    => 0
    | .vec128 => ⟨Array.replicate 16 0, by simp⟩

/-- Primitive memory effects, parameterised by `var : ProgTy → Type`.

    Read operations return `var τ` (a symbolic value in compilation mode,
    a concrete value in execution mode).  Write operations always return `Unit`.

    `vloadA`/`vstoreA` are semantically identical to `vload`/`vstore` —
    alignment is a precondition enforced by the caller. -/
inductive MemOp (var : ProgTy → Type) : Type → Type where
  | peekU8    : var .nat → MemOp var (var .u8)
  | pokeU8    : var .nat → var .u8   → MemOp var Unit
  | peekU32le : var .nat → MemOp var (var .u32)
  | pokeU32le : var .nat → var .u32  → MemOp var Unit
  | vload     : var .nat → MemOp var (var .vec128)
  | vloadA    : var .nat → MemOp var (var .vec128)
  | vstore    : var .nat → var .vec128 → MemOp var Unit
  | vstoreA   : var .nat → var .vec128 → MemOp var Unit
  /-- Create a Vec128 from a compile-time constant.  Compiles to `_mm_set_epi8(...)`. -/
  | vconst    : Vec128 → MemOp var (var .vec128)

def MemOp.exec : MemOp ProgTy.Ty α → Heap → (α × Heap)
  | .peekU8 addr, h => (h.read addr, h)
  | .pokeU8 addr val, h => ((), h.write addr val)
  | .peekU32le addr, h =>
      let b i := (h.read (addr + i)).toUInt32
      (b 3 <<< 24 ||| b 2 <<< 16 ||| b 1 <<< 8 ||| b 0, h)
  | .pokeU32le addr val, h =>
      let h' := h
        |>.write addr       val.toUInt8
        |>.write (addr + 1) (val >>> 8).toUInt8
        |>.write (addr + 2) (val >>> 16).toUInt8
        |>.write (addr + 3) (val >>> 24).toUInt8
      ((), h')
  | .vload addr, h | .vloadA addr, h =>
      (Vector.ofFn (fun i : Fin 16 => h.read (addr + i.val)), h)
  | .vstore addr v, h | .vstoreA addr v, h =>
      let h' := List.finRange 16 |>.foldl (fun acc i => acc.write (addr + i.val) v[i]) h
      ((), h')
  | .vconst v, h => (v, h)

end RightByte
