import RightByte.Mem.MemOp
import Mathlib.Data.Finmap
import Mathlib.Data.List.FinRange

namespace RightByte

/-! ## Lightweight Separation Logic over `Heap`

We use a *read-agreement* formulation of `arrayAt`:
`arrayAt base vs h` semantically means every address `base+i` for `i < vs.length`
reads back `vs[i]!` in `h`.  Other addresses in `h` are unconstrained.

This is weaker than requiring `h.keys = Finset.Ico base (base + n)`, but
sufficient for our correctness theorems and easier to work with. -/

/-- Predicate on heaps. -/
abbrev HeapProp := Heap → Prop

/-- Separating conjunction: `P ⋆ Q` holds on `h` when `h` splits into disjoint
    parts `h1`, `h2` satisfying `P` and `Q` respectively. -/
def sep (P Q : HeapProp) : HeapProp :=
  fun h => ∃ h1 h2, h1.Disjoint h2 ∧ h = h1 ∪ h2 ∧ P h1 ∧ Q h2

scoped notation:35 P " ⋆ " Q => sep P Q

/-- The empty heap. -/
def emp : HeapProp := fun h => h = ∅

/-- `arrayAt base vs h`: `h` contains the bytes `vs` starting at `base`. -/
def arrayAt (base : Nat) (vs : List UInt8) : HeapProp :=
  fun h => ∀ i < vs.length, h.read (base + i) = vs[i]!

-- ---------------------------------------------------------------------------
-- Foundation: read/write lemmas for Heap
-- ---------------------------------------------------------------------------

lemma Heap.read_write_eq (h : Heap) (a : Nat) (v : UInt8) :
    (h.write a v).read a = v := by
  simp [Heap.read, Heap.write, Finmap.lookup_insert]

lemma Heap.read_write_ne (h : Heap) (a a' : Nat) (v : UInt8) (hne : a' ≠ a) :
    (h.write a v).read a' = h.read a' := by
  simp only [Heap.read, Heap.write]
  rw [Finmap.lookup_insert_of_ne h hne]

-- ---------------------------------------------------------------------------
-- Core foldl lemma (basis for vstore_frame)
-- ---------------------------------------------------------------------------

/-- A sequential foldl of writes to `[base, base+n)` does not affect address `a`
    when `a` is outside that range.  Proved by induction on the list. -/
lemma foldl_write_ne {n : Nat} (base : Nat) (vals : Fin n → UInt8) (h₀ : Heap) (a : Nat)
    (hout : ∀ i : Fin n, a ≠ base + i.val) :
    Heap.read
      ((List.finRange n).foldl (fun acc i => Heap.write acc (base + i.val) (vals i)) h₀)
      a = Heap.read h₀ a := by
  suffices key : ∀ (ls : List (Fin n)) (h : Heap),
      (∀ i ∈ ls, a ≠ base + i.val) →
      Heap.read
        (ls.foldl (fun acc i => Heap.write acc (base + i.val) (vals i)) h)
        a = Heap.read h a by
    exact key (List.finRange n) h₀ (fun i _ => hout i)
  intro ls
  induction ls with
  | nil => simp
  | cons i is ih =>
      intro h hmem
      simp only [List.foldl_cons]
      rw [ih (Heap.write h (base + i.val) (vals i))
              (fun j hj => hmem j (List.mem_cons_of_mem i hj))]
      exact Heap.read_write_ne h (base + i.val) a (vals i)
               (hmem i List.mem_cons_self)

-- ---------------------------------------------------------------------------
-- arrayAt lemmas
-- ---------------------------------------------------------------------------

/-- Read from an `arrayAt` heap at a valid index. -/
lemma arrayAt_read (base : Nat) (vs : List UInt8) (h : Heap) (i : Nat) (hi : i < vs.length) :
    arrayAt base vs h → h.read (base + i) = vs[i]! :=
  fun harr => harr i hi

/-- `getElem!` for `xs ++ ys` when `i < xs.length`. -/
private lemma getElem!_append_left' (xs ys : List UInt8) (i : Nat) (h : i < xs.length) :
    (xs ++ ys)[i]! = xs[i]! := by
  rw [getElem!_pos (xs ++ ys) i (by simp; omega),
      getElem!_pos xs i h,
      List.getElem_append_left h]

/-- `getElem!` for `xs ++ ys` when `xs.length ≤ i`. -/
private lemma getElem!_append_right' (xs ys : List UInt8) (i : Nat)
    (hge : xs.length ≤ i) (hlt : i - xs.length < ys.length) :
    (xs ++ ys)[i]! = ys[i - xs.length]! := by
  rw [getElem!_pos (xs ++ ys) i (by simp; omega),
      getElem!_pos ys (i - xs.length) hlt,
      List.getElem_append_right hge]

/-- `arrayAt` splits at a list append boundary. -/
lemma arrayAt_append (base : Nat) (xs ys : List UInt8) (h : Heap) :
    arrayAt base (xs ++ ys) h ↔ arrayAt base xs h ∧ arrayAt (base + xs.length) ys h := by
  constructor
  · intro hall
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [← getElem!_append_left' xs ys i hi]
      exact hall i (by simp; omega)
    · have key : (xs ++ ys)[xs.length + i]! = ys[i]! := by
        have := getElem!_append_right' xs ys (xs.length + i) (by omega) (by omega)
        simp only [Nat.add_sub_cancel_left] at this
        exact this
      have := hall (xs.length + i) (by simp; omega)
      rw [key] at this
      rwa [show base + xs.length + i = base + (xs.length + i) from by omega]
  · intro ⟨hxs, hys⟩ i hi
    simp only [List.length_append] at hi
    by_cases hlt : i < xs.length
    · rw [getElem!_append_left' xs ys i hlt]
      exact hxs i hlt
    · have hge : xs.length ≤ i := by omega
      have hyi : i - xs.length < ys.length := by omega
      rw [getElem!_append_right' xs ys i hge hyi]
      have := hys (i - xs.length) hyi
      simp only [show base + xs.length + (i - xs.length) = base + i from by omega] at this
      exact this

/-- Writing outside `[base, base + vs.length)` preserves `arrayAt`. -/
lemma arrayAt_write_outside (base : Nat) (vs : List UInt8) (h : Heap) (a : Nat) (v : UInt8)
    (hout : ∀ i < vs.length, a ≠ base + i) :
    arrayAt base vs h → arrayAt base vs (h.write a v) := by
  intro harr i hi
  rw [Heap.read_write_ne h a (base + i) v (Ne.symm (hout i hi))]
  exact harr i hi

-- ---------------------------------------------------------------------------
-- Frame lemmas for MemOp effects
-- ---------------------------------------------------------------------------

/-- `vstore` only modifies `[addr, addr+16)`. -/
lemma vstore_frame (addr : Nat) (v : Vec128) (h : Heap) (a : Nat)
    (hout : ¬ (addr ≤ a ∧ a < addr + 16)) :
    Heap.read (MemOp.exec (.vstore addr v) h).2 a = Heap.read h a := by
  simp only [MemOp.exec]
  apply foldl_write_ne
  intro ⟨i, hi⟩
  simp only
  omega

/-- `pokeU8` only modifies address `addr`. -/
lemma pokeU8_frame (addr : Nat) (v : UInt8) (h : Heap) (a : Nat) (hne : a ≠ addr) :
    Heap.read (MemOp.exec (.pokeU8 addr v) h).2 a = Heap.read h a := by
  simp [MemOp.exec, Heap.read_write_ne h addr a v hne]

end RightByte
