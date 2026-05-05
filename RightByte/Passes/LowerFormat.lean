import RightByte.Format.Parse
import RightByte.Mem.Prog

namespace RightByte

abbrev Ptr := Nat

/-- Extract `n` bytes from the heap at `src` as a `ByteArray`. -/
def heapSlice (σ : Heap) (src n : Nat) : ByteArray :=
  ⟨Array.ofFn (fun i : Fin n => σ.read (src + i.val))⟩

private def readNatFromHeap (src : Ptr) (byteCount : Nat) : ProgExec Nat :=
  (List.range byteCount).foldlM (fun acc i => do
    let b ← Prog.effect (.peekU8 (src + i))
    pure (acc ||| b.toNat <<< (8 * i))) 0

mutual

private partial def lowerRepN (f : Format τ) : (n : Nat) → Ptr → ProgExec (Vector τ.Ty n × Ptr)
  | 0,     ptr => pure (⟨#[], rfl⟩, ptr)
  | n + 1, ptr => do
      let (xs, ptr')  ← lowerRepN f n ptr
      let (x,  ptr'') ← lowerFormatWithOffset f ptr'
      pure (xs.push x, ptr'')

/-- Lower `Format τ` to a `ProgExec` that reads `τ.Ty` from `src` and returns
    the value together with the offset past the last byte consumed. -/
partial def lowerFormatWithOffset : Format τ → Ptr → ProgExec (τ.Ty × Ptr)
  | .u8, src => do
      let b ← Prog.effect (.peekU8 src)
      pure (b, src + 1)
  | .u16le, src => do
      let b0 ← Prog.effect (.peekU8 src)
      let b1 ← Prog.effect (.peekU8 (src + 1))
      pure (b1.toUInt16 <<< 8 ||| b0.toUInt16, src + 2)
  | .u32le, src => do
      let v ← Prog.effect (.peekU32le src)
      pure (v, src + 4)
  | .u32be, src => do
      let b0 ← Prog.effect (.peekU8 src)
      let b1 ← Prog.effect (.peekU8 (src + 1))
      let b2 ← Prog.effect (.peekU8 (src + 2))
      let b3 ← Prog.effect (.peekU8 (src + 3))
      pure (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32, src + 4)
  | .u64le, src => do
      let b i := (·.toUInt64) <$> Prog.effect (.peekU8 (src + i))
      let b0 ← b 0; let b1 ← b 1; let b2 ← b 2; let b3 ← b 3
      let b4 ← b 4; let b5 ← b 5; let b6 ← b 6; let b7 ← b 7
      pure (b7 <<< (56 : UInt64) ||| b6 <<< (48 : UInt64) ||| b5 <<< (40 : UInt64) |||
            b4 <<< (32 : UInt64) ||| b3 <<< (24 : UInt64) ||| b2 <<< (16 : UInt64) |||
            b1 <<< (8 : UInt64)  ||| b0, src + 8)
  | .bits n, src => do
      let byteCount := (n + 7) / 8
      let nat ← readNatFromHeap src byteCount
      pure (BitVec.ofNat n nat, src + byteCount)
  | .seq f g, src => do
      let (x, src')  ← lowerFormatWithOffset f src
      let (y, src'') ← lowerFormatWithOffset g src'
      pure ((x, y), src'')
  | .rep n f, src => do
      let (vec, src') ← lowerRepN f n src
      pure (vec, src')
  | .aligned n f, src =>
      let aligned := src + (n - src % n) % n
      lowerFormatWithOffset f aligned
  | .lengthPrefixed lenF f, src => do
      let (len, src') ← lowerFormatWithOffset lenF src
      let (val, _)   ← lowerFormatWithOffset f src'
      pure (val, src' + len.toNat)
  | .countPrefixed lenF f, src => do
      let (count, src')  ← lowerFormatWithOffset lenF src
      let (vec,   src'') ← lowerRepN f count.toNat src'
      pure (vec.1, src'')
  | .tagUnion eq tagF table, src => do
      let (tag, src') ← lowerFormatWithOffset tagF src
      match table.find eq tag with
      | none     => Prog.abort s!"tagUnion: unrecognised tag"
      | some fmt => do
          let (val, src'') ← lowerFormatWithOffset fmt src'
          pure ((tag, val), src'')

end

def lowerFormat (f : Format τ) (src : Ptr) : ProgExec τ.Ty :=
  Prod.fst <$> lowerFormatWithOffset f src

def lowerFormatDynamic (f : Format τ) (src : Ptr) : ProgExec τ.Ty :=
  lowerFormat f src

theorem lowerFormat_correct (f : Format τ) (src : Ptr) (n : Nat) (σ : Heap) :
    (ProgExec.exec (lowerFormat f src) σ).map Prod.fst =
    (f.parse (heapSlice σ src n) 0).map Prod.fst := by
  sorry

end RightByte
