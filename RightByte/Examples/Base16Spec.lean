import RightByte.Mem.Prog
import RightByte.Mem.Symbolic
import RightByte.Mem.SepLogic
import RightByte.Examples.Base16
import Mathlib.Tactic

namespace RightByte.Examples

/-! ## Pure functional specification for base-16 encoding -/

-- ---------------------------------------------------------------------------
-- Pure spec
-- ---------------------------------------------------------------------------

/-- Nibble to ASCII: `n + 48 + (n / 10) * 39`.
    Gives '0'–'9' for 0–9 and 'a'–'f' for 10–15. -/
def nibbleToAscii (n : Nat) : UInt8 :=
  (n + 48 + (n / 10) * 39).toUInt8

/-- `nibbleToAscii` agrees with `hexLUT` for all valid nibbles. -/
theorem nibbleToAscii_eq_lut (n : Nat) (hn : n < 16) :
    nibbleToAscii n = hexLUT.get ⟨n, hn⟩ := by
  interval_cases n <;> rfl

/-- Pure spec for one byte: returns `(hi_ascii, lo_ascii)`. -/
def base16ByteSpec (b : UInt8) : UInt8 × UInt8 :=
  (nibbleToAscii (b.toNat >>> 4), nibbleToAscii (b.toNat &&& 0xF))

/-- Pure spec for a list: each byte expands to two ASCII characters. -/
def base16Spec (vs : List UInt8) : List UInt8 :=
  vs.flatMap fun b => let (hi, lo) := base16ByteSpec b; [hi, lo]

theorem base16Spec_length (vs : List UInt8) :
    (base16Spec vs).length = 2 * vs.length := by
  induction vs with
  | nil => simp [base16Spec]
  | cons b bs ih =>
      simp only [base16Spec] at ih ⊢
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
      omega

-- ---------------------------------------------------------------------------
-- Scalar implementation (tail loop factored out)
-- ---------------------------------------------------------------------------

/-- Scalar base-16 encoder: encodes `len` bytes from `src` to `dst`. -/
def base16ScalarAll {var : ProgTy → Type} [Symbolic var]
    (src dst len : var .nat) : Prog var Unit :=
  Prog.forVarN len fun i => do
    let byte   ← Prog.effect (.peekU8 (Symbolic.addNat src i))
    let w      := Symbolic.u8ToNat byte
    let hi     := Symbolic.shrNat w (Symbolic.litNat 4)
    let lo     := Symbolic.andNat w (Symbolic.litNat 0xF)
    let dstOff := Symbolic.addNat dst (Symbolic.mulNat i (Symbolic.litNat 2))
    Prog.effect (.pokeU8 dstOff (Symbolic.natToU8 (toAscii hi)))
    Prog.effect (.pokeU8 (Symbolic.addNat dstOff (Symbolic.litNat 1))
                         (Symbolic.natToU8 (toAscii lo)))

-- ---------------------------------------------------------------------------
-- Concrete loop step (for proofs)
-- Uses i*2 to match Symbolic.mulNat i (litNat 2) = i * 2 under ProgTy.Ty.
-- ---------------------------------------------------------------------------

private abbrev loopStep (src dst : Nat) : Heap → Nat → Heap :=
  fun acc i =>
    ((ProgExec.exec
      (do let byte   ← Prog.effect (.peekU8 (src + i))
          let w      := (byte.toNat : Nat)
          let hi     := w >>> 4
          let lo     := w &&& 0xF
          let dstOff := dst + i * 2
          Prog.effect (.pokeU8 dstOff     (Symbolic.natToU8 (toAscii hi)))
          Prog.effect (.pokeU8 (dstOff+1) (Symbolic.natToU8 (toAscii lo))))
      acc).map Prod.snd).getD acc

private lemma loopStep_write_hi (src dst k : Nat) (h : Heap) :
    (loopStep src dst h k).read (dst + k*2) = nibbleToAscii ((h.read (src + k)).toNat >>> 4) := by
  sorry

private lemma loopStep_write_lo (src dst k : Nat) (h : Heap) :
    (loopStep src dst h k).read (dst + k*2 + 1) = nibbleToAscii ((h.read (src + k)).toNat &&& 0xF) := by
  sorry

private lemma loopStep_frame (src dst k : Nat) (h : Heap) (a : Nat)
    (ha1 : a ≠ dst + k*2) (ha2 : a ≠ dst + k*2 + 1) :
    (loopStep src dst h k).read a = h.read a := by
  sorry

-- ---------------------------------------------------------------------------
-- Frame lemma: foldl of loopStep leaves address a unchanged if
-- a is outside all write ranges.
-- ---------------------------------------------------------------------------

lemma foldl_loopStep_frame (src dst k : Nat) (h : Heap) (a : Nat)
    (hout : ∀ i < k, a ≠ dst + i*2 ∧ a ≠ dst + i*2 + 1) :
    ((List.range k).foldl (loopStep src dst) h).read a = h.read a := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [loopStep_frame src dst k _ a (hout k (Nat.lt_succ_self k)).1
                                       (hout k (Nat.lt_succ_self k)).2]
      exact ih (fun i hi => hout i (Nat.lt_succ_of_lt hi))

-- ---------------------------------------------------------------------------
-- base16ScalarAll exec = foldl of loopStep (definitional equality)
-- ---------------------------------------------------------------------------

lemma base16ScalarAll_exec_eq (src dst n : Nat) (h : Heap) :
    ((ProgExec.exec (base16ScalarAll src dst n) h).map Prod.snd).getD h =
    (List.range n).foldl (loopStep src dst) h := by
  sorry

-- ---------------------------------------------------------------------------
-- Loop correctness invariant
-- ---------------------------------------------------------------------------

/-- After n iterations of the scalar loop, positions `dst + k*2` and
    `dst + k*2 + 1` (for `k < n`) hold the correct nibble-to-ASCII values. -/
lemma scalar_loop_all_correct (src dst : Nat) (h : Heap) (vs : List UInt8)
    (hsrc : arrayAt src vs h)
    (hdisj : ∀ i < vs.length, ∀ j < 2 * vs.length, src + i ≠ dst + j)
    (n : Nat) (hn : n ≤ vs.length) :
    ∀ k < n,
      ((List.range n).foldl (loopStep src dst) h).read (dst + k*2)     = nibbleToAscii (vs[k]!.toNat >>> 4) ∧
      ((List.range n).foldl (loopStep src dst) h).read (dst + k*2 + 1) = nibbleToAscii (vs[k]!.toNat &&& 0xF) := by
  induction n with
  | zero => intro k hk; omega
  | succ n ihn =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      intro k hk
      by_cases hkn : k < n
      · have ⟨ih1, ih2⟩ := ihn (Nat.le_of_succ_le hn) k hkn
        exact ⟨by rw [loopStep_frame src dst n _ _ (by omega) (by omega)]; exact ih1,
               by rw [loopStep_frame src dst n _ _ (by omega) (by omega)]; exact ih2⟩
      · have hkn : k = n := by omega
        have src_unchanged : ((List.range n).foldl (loopStep src dst) h).read (src + n) = h.read (src + n) :=
          foldl_loopStep_frame src dst n h (src + n)
            (fun i hi => ⟨hdisj n (Nat.lt_of_succ_le hn) (i*2)   (by omega),
                          hdisj n (Nat.lt_of_succ_le hn) (i*2+1) (by omega)⟩)
        have src_val : h.read (src + n) = vs[n]! := hsrc n (Nat.lt_of_succ_le hn)
        rw [hkn]
        exact ⟨by rw [loopStep_write_hi, src_unchanged, src_val],
               by rw [loopStep_write_lo, src_unchanged, src_val]⟩

-- ---------------------------------------------------------------------------
-- Spec index lemmas
-- ---------------------------------------------------------------------------

private lemma flatMap_pairs_even (vs : List UInt8)
    (f g : UInt8 → UInt8) (k : Nat) (hk : k < vs.length) :
    (vs.flatMap (fun b => [f b, g b]))[k*2]! = f vs[k]! := by
  induction vs generalizing k with
  | nil => simp at hk
  | cons b bs ih =>
      simp only [List.flatMap_cons]
      cases k with
      | zero => simp
      | succ k =>
          have hk' : k < bs.length := by simp [List.length_cons] at hk; omega
          rw [show k.succ * 2 = k * 2 + 1 + 1 by omega]
          simp only [List.getElem!_cons_succ, List.getElem!_cons_succ]
          exact ih k hk'

private lemma flatMap_pairs_odd (vs : List UInt8)
    (f g : UInt8 → UInt8) (k : Nat) (hk : k < vs.length) :
    (vs.flatMap (fun b => [f b, g b]))[k*2 + 1]! = g vs[k]! := by
  induction vs generalizing k with
  | nil => simp at hk
  | cons b bs ih =>
      simp only [List.flatMap_cons]
      cases k with
      | zero => simp
      | succ k =>
          have hk' : k < bs.length := by simp [List.length_cons] at hk; omega
          rw [show k.succ * 2 + 1 = k * 2 + 1 + 1 + 1 by omega]
          simp only [List.getElem!_cons_succ, List.getElem!_cons_succ, List.getElem!_cons_succ]
          exact ih k hk'

lemma base16Spec_get_hi (vs : List UInt8) (k : Nat) (hk : k < vs.length) :
    (base16Spec vs)[k*2]! = nibbleToAscii (vs[k]!.toNat >>> 4) :=
  flatMap_pairs_even vs _ _ k hk

lemma base16Spec_get_lo (vs : List UInt8) (k : Nat) (hk : k < vs.length) :
    (base16Spec vs)[k*2 + 1]! = nibbleToAscii (vs[k]!.toNat &&& 0xF) :=
  flatMap_pairs_odd vs _ _ k hk

-- ---------------------------------------------------------------------------
-- Scalar correctness theorem
-- ---------------------------------------------------------------------------

/-- After running `base16ScalarAll src dst vs.length` on a heap satisfying
    `arrayAt src vs`, every output byte at `dst + i` (for `i < 2 * vs.length`)
    equals `(base16Spec vs)[i]!`.

    **Precondition**: src and dst regions don't overlap. -/
theorem base16Scalar_correct (src dst : Nat) (h : Heap) (vs : List UInt8)
    (hsrc : arrayAt src vs h)
    (hdisj : ∀ i < vs.length, ∀ j < 2 * vs.length, src + i ≠ dst + j) :
    let h' := ((ProgExec.exec (base16ScalarAll src dst vs.length) h).map Prod.snd).getD h
    ∀ i < 2 * vs.length, h'.read (dst + i) = (base16Spec vs)[i]! := by
  intro h' i hi
  have heq : h' = (List.range vs.length).foldl (loopStep src dst) h :=
    base16ScalarAll_exec_eq src dst vs.length h
  rw [heq]
  obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < vs.length, i = k * 2 ∨ i = k * 2 + 1 :=
    ⟨i / 2, by omega, by omega⟩
  · have ⟨hval, _⟩ := scalar_loop_all_correct src dst h vs hsrc hdisj vs.length le_rfl k hk
    rw [hval, base16Spec_get_hi vs k hk]
  · rw [show dst + (k * 2 + 1) = dst + k * 2 + 1 from by omega]
    have ⟨_, hval⟩ := scalar_loop_all_correct src dst h vs hsrc hdisj vs.length le_rfl k hk
    rw [hval, base16Spec_get_lo vs k hk]

end RightByte.Examples
