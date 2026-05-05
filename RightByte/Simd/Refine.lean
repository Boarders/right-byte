import RightByte.Mem.SepLogic
import RightByte.Simd.VecOp

namespace RightByte

/-! ## General per-lane SIMD refinement framework

A `VecLaneFn` bundles a `Vec128 → Vec128` SIMD pipeline with a `UInt8 → UInt8` scalar spec
and a proof that the two agree pointwise on every lane satisfying the precondition `pre`.

The two general replacement theorems are:

- `vecMap_correct`: a single SIMD map (load / apply / store) refines a scalar 16-byte loop.
- `vecExpand2_correct`: two SIMD maps followed by `unpacklo8`/`unpackhi8` interleaving refine
  a scalar loop that expands each byte to two output bytes.

Any caller that can provide the right `VecLaneFn` instances gets correctness for free.
-/

-- ---------------------------------------------------------------------------
-- Core structure
-- ---------------------------------------------------------------------------

/-- A vectorized per-lane byte function.

    - `spec` : the scalar `UInt8 → UInt8` semantics
    - `impl` : the `Vec128 → Vec128` SIMD implementation
    - `pre`  : a precondition on individual input bytes (e.g. "high bit clear" for pshufb);
               use `fun _ => True` for unconditional operations
    - `correct` : for every lane `i` whose value satisfies `pre`, `impl v` agrees with `spec`
-/
structure VecLaneFn where
  spec    : UInt8 → UInt8
  impl    : Vec128 → Vec128
  pre     : UInt8 → Prop
  correct : ∀ (v : Vec128) (i : Fin 16), pre v[i] → (impl v)[i] = spec v[i]

-- ---------------------------------------------------------------------------
-- Helper: foldl write / read lemmas not already in SepLogic
-- ---------------------------------------------------------------------------

/-- Reading address `base + k.val` after a sequential foldl of writes to
    `base+0 .. base+n-1` gives the value written at step `k`. -/
private lemma foldl_write_eq {n : Nat} (base : Nat) (vals : Fin n → UInt8)
    (h₀ : Heap) (k : Fin n) :
    ((List.finRange n).foldl (fun acc i => acc.write (base + i.val) (vals i)) h₀).read
      (base + k.val) = vals k := by
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
      rw [List.finRange_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases hkn : k.val = n
      · -- k is the last element; its write is not overwritten
        subst hkn
        have hk : k = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext rfl
        subst hk
        rw [foldl_write_ne]
        · exact Heap.read_write_eq _ _ _
        · intro ⟨i, hi⟩; simp; omega
      · -- k.val < n; the final write at n is at a different address
        have hlt : k.val < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp k.isLt) hkn
        rw [Heap.read_write_ne _ _ _ _ (by omega)]
        -- use the IH on the inner foldl over finRange n
        -- the vals for the inner foldl agree with vals ∘ Fin.castSucc
        have : ((List.finRange n).foldl (fun acc i => acc.write (base + i.val)
            (vals (Fin.castSucc i))) h₀).read (base + k.val) = vals (Fin.castSucc ⟨k.val, hlt⟩) := by
          exact ih (fun i => vals (Fin.castSucc i)) h₀ ⟨k.val, hlt⟩
        simp [Fin.castSucc, Fin.val] at this
        exact this

/-- Reading `addr + k.val` from the result of `vstore addr v` gives `v[k]`. -/
lemma vstore_read (addr : Nat) (v : Vec128) (h : Heap) (k : Fin 16) :
    (MemOp.exec (.vstore addr v) h).2.read (addr + k.val) = v[k] := by
  simp only [MemOp.exec]
  exact foldl_write_eq addr (fun i => v[i]) h k

-- ---------------------------------------------------------------------------
-- Standard VecLaneFn instances
-- ---------------------------------------------------------------------------

/-- Bitwise AND with a constant mask — unconditional. -/
def andLaneFn (mask : UInt8) : VecLaneFn where
  spec    := (· &&& mask)
  impl    := fun v => VecOp.scalarSem .and128 ⟨#[v, Vector.replicate 16 mask], by simp⟩
  pre     := fun _ => True
  correct := by
    intro v i _
    simp only [VecOp.scalarSem, Vector.getElem_zipWith, Vector.getElem_replicate]

/-- Low nibble extraction: `b &&& 0x0F`. -/
def loNibbleLaneFn : VecLaneFn := andLaneFn 0x0F

private lemma hiNibble_even (a b : UInt8) :
    ((b.toUInt16 <<< (8 : UInt16) ||| a.toUInt16) >>> (4 : UInt16)).toUInt8 &&& 0x0F =
    a >>> 4 := by decide

private lemma hiNibble_odd (a b : UInt8) :
    (((b.toUInt16 <<< (8 : UInt16) ||| a.toUInt16) >>> (4 : UInt16)) >>>
      (8 : UInt16)).toUInt8 &&& 0x0F = b >>> 4 := by decide

/-- High nibble extraction: `shr16_128 4` followed by `and128 0x0F`.

    Despite `shr16_128` operating on 16-bit lanes (mixing adjacent byte pairs),
    the subsequent mask restores per-byte semantics: `(result)[i] = v[i] >>> 4`. -/
def hiNibbleLaneFn : VecLaneFn where
  spec    := (· >>> 4)
  impl    := fun v =>
    let shifted := VecOp.scalarSem (.shr16_128 4) ⟨#[v], by simp⟩
    VecOp.scalarSem .and128 ⟨#[shifted, Vector.replicate 16 0x0F], by simp⟩
  pre     := fun _ => True
  correct := by
    intro v i _
    simp only [VecOp.scalarSem, applyLane16, Vector.getElem_ofFn,
               Vector.getElem_zipWith, Vector.getElem_replicate]
    split
    · -- i.val % 2 = 0: even lane, reads from the low byte of the 16-bit lane
      rename_i heven
      have h0 : i.val / 2 * 2 < 16 := by omega
      have h1 : i.val / 2 * 2 + 1 < 16 := by omega
      rw [show v[i] = v[⟨i.val / 2 * 2, h0⟩] from by congr 1; ext; omega]
      exact hiNibble_even v[⟨i.val / 2 * 2, h0⟩] v[⟨i.val / 2 * 2 + 1, h1⟩]
    · -- i.val % 2 = 1: odd lane, reads from the high byte of the 16-bit lane
      rename_i hodd
      have h0 : i.val / 2 * 2 < 16 := by omega
      have h1 : i.val / 2 * 2 + 1 < 16 := by omega
      rw [show v[i] = v[⟨i.val / 2 * 2 + 1, h1⟩] from by congr 1; ext; omega]
      exact hiNibble_odd v[⟨i.val / 2 * 2, h0⟩] v[⟨i.val / 2 * 2 + 1, h1⟩]

/-- Table lookup via `pshufb` (shuffle128).

    Precondition: the input byte's high bit is 0 (nibble-valid input), so pshufb
    does not zero out the output lane.

    `spec b = lut[b.toNat &&& 0xF]!` — looks up `b`'s low 4 bits in the table. -/
def pshufbLaneFn (lut : Vec128) : VecLaneFn where
  spec    := fun b => lut[(b.toNat &&& 0xF)]!
  impl    := fun v => VecOp.scalarSem .shuffle128 ⟨#[lut, v], by simp⟩
  pre     := fun b => b &&& 0x80 = 0
  correct := by
    intro v i hpre
    simp only [VecOp.scalarSem, Vector.getElem_ofFn]
    have hno : ¬ (v[i] &&& 0x80 ≠ 0) := by simp [hpre]
    simp only [hno, not_false_eq_true, ↓reduceIte]
    congr 1
    -- (v[i] &&& 0x0F).toNat = v[i].toNat &&& 0xF
    omega

-- ---------------------------------------------------------------------------
-- Composition
-- ---------------------------------------------------------------------------

/-- Compose two `VecLaneFn`s: apply `g` first, then `f`.

    The composed precondition requires `g`'s precondition on the input and
    `f`'s precondition on `g`'s output. -/
def VecLaneFn.comp (f g : VecLaneFn) : VecLaneFn where
  spec    := f.spec ∘ g.spec
  impl    := f.impl ∘ g.impl
  pre     := fun b => g.pre b ∧ f.pre (g.spec b)
  correct := fun v i ⟨hg, hf⟩ => by
    rw [Function.comp_apply, ← g.correct v i hg]
    exact f.correct (g.impl v) i hf

-- ---------------------------------------------------------------------------
-- General replacement theorem 1: VecMap
-- ---------------------------------------------------------------------------

/-- **VecMap**: a single SIMD map refines a scalar 16-byte point-map loop.

    If `f.pre` holds on all 16 input bytes, then the SIMD pipeline
    `h' = vstore dst (f.impl (vload src h))` produces the same byte at
    `dst + k` as a scalar loop writing `f.spec input[k]` at each position. -/
theorem vecMap_correct (f : VecLaneFn) (src dst : Nat) (h : Heap) (vs : List UInt8)
    (hvs : vs.length = 16) (hsrc : arrayAt src vs h)
    (hpre : ∀ i : Fin 16, f.pre vs[i.val]!)
    (hdisj : ∀ i < 16, ∀ j < 16, src + i ≠ dst + j) :
    let v  := Vector.ofFn (fun i : Fin 16 => vs[i.val]!)
    let h' := (MemOp.exec (.vstore dst (f.impl v)) h).2
    ∀ k < 16, h'.read (dst + k) = f.spec vs[k]! := by
  intro v h' k hk
  have hk16 : k < 16 := hk
  have hread : h'.read (dst + k) = (f.impl v)[⟨k, hk16⟩] := by
    show (MemOp.exec (.vstore dst (f.impl v)) h).2.read (dst + k) = _
    rw [vstore_read dst (f.impl v) h ⟨k, hk16⟩]
  rw [hread]
  rw [f.correct v ⟨k, hk16⟩ (by simp [v, hpre ⟨k, hk16⟩])]

-- ---------------------------------------------------------------------------
-- Helper: unpacklo8 / unpackhi8 index lemmas
-- ---------------------------------------------------------------------------

private lemma unpacklo8_even (a b : Vec128) (k : Fin 8) :
    (VecOp.scalarSem .unpacklo8 ⟨#[a, b], by simp⟩)[⟨k.val * 2, by omega⟩] = a[k.castAdd 8] := by
  simp [VecOp.scalarSem, Vector.getElem_ofFn]
  omega

private lemma unpacklo8_odd (a b : Vec128) (k : Fin 8) :
    (VecOp.scalarSem .unpacklo8 ⟨#[a, b], by simp⟩)[⟨k.val * 2 + 1, by omega⟩] = b[k.castAdd 8] := by
  simp [VecOp.scalarSem, Vector.getElem_ofFn]
  omega

private lemma unpackhi8_even (a b : Vec128) (k : Fin 8) :
    (VecOp.scalarSem .unpackhi8 ⟨#[a, b], by simp⟩)[⟨k.val * 2, by omega⟩] = a[⟨8 + k.val, by omega⟩] := by
  simp [VecOp.scalarSem, Vector.getElem_ofFn]
  omega

private lemma unpackhi8_odd (a b : Vec128) (k : Fin 8) :
    (VecOp.scalarSem .unpackhi8 ⟨#[a, b], by simp⟩)[⟨k.val * 2 + 1, by omega⟩] = b[⟨8 + k.val, by omega⟩] := by
  simp [VecOp.scalarSem, Vector.getElem_ofFn]
  omega

-- ---------------------------------------------------------------------------
-- General replacement theorem 2: VecExpand2
-- ---------------------------------------------------------------------------

/-- **VecExpand2**: two SIMD maps with `unpacklo8`/`unpackhi8` interleaving refine a
    scalar loop that expands each input byte to two output bytes.

    After two `vstore`s:
    - `vstore dst (unpacklo8 (fHi.impl v) (fLo.impl v))` — bytes 0..15
    - `vstore (dst+16) (unpackhi8 (fHi.impl v) (fLo.impl v))` — bytes 16..31

    every output pair `(dst+k*2, dst+k*2+1)` holds `(fHi.spec vs[k]!, fLo.spec vs[k]!)`.

    This directly generalises the SIMD base-16 encoding pattern. -/
theorem vecExpand2_correct (fHi fLo : VecLaneFn) (src dst : Nat) (h : Heap) (vs : List UInt8)
    (hvs : vs.length = 16) (hsrc : arrayAt src vs h)
    (hpreHi : ∀ i : Fin 16, fHi.pre vs[i.val]!)
    (hpreLo : ∀ i : Fin 16, fLo.pre vs[i.val]!)
    (hdisj : ∀ i < 16, ∀ j < 32, src + i ≠ dst + j) :
    let v     := Vector.ofFn (fun i : Fin 16 => vs[i.val]!)
    let hiVec := fHi.impl v
    let loVec := fLo.impl v
    let outLo := VecOp.scalarSem .unpacklo8 ⟨#[hiVec, loVec], by simp⟩
    let outHi := VecOp.scalarSem .unpackhi8 ⟨#[hiVec, loVec], by simp⟩
    let h'    := (MemOp.exec (.vstore (dst + 16) outHi)
                  (MemOp.exec (.vstore dst outLo) h).2).2
    ∀ k < 16,
      h'.read (dst + k * 2)     = fHi.spec vs[k]! ∧
      h'.read (dst + k * 2 + 1) = fLo.spec vs[k]! := by
  intro v hiVec loVec outLo outHi h' k hk
  -- Abbreviate the two intermediate heaps
  set h1 := (MemOp.exec (.vstore dst outLo) h).2 with hh1
  -- The two stores write to disjoint ranges [dst,dst+15] and [dst+16,dst+31]
  -- We split on k < 8 (bytes come from outLo) vs k ≥ 8 (bytes come from outHi)
  by_cases hk8 : k < 8
  · -- Both dst+k*2 and dst+k*2+1 are < dst+16, so the outer vstore (at dst+16) is a frame.
    have hlo_hi : ¬ (dst + 16 ≤ dst + k * 2 ∧ dst + k * 2 < dst + 16 + 16) := by omega
    have hlo_lo : ¬ (dst + 16 ≤ dst + k * 2 + 1 ∧ dst + k * 2 + 1 < dst + 16 + 16) := by omega
    rw [show dst + k * 2 = dst + k * 2 from rfl,
        vstore_frame (dst + 16) outHi h1 (dst + k * 2) hlo_hi,
        vstore_frame (dst + 16) outHi h1 (dst + k * 2 + 1) hlo_lo]
    -- Now read from h1 = vstore(dst, outLo, h)
    let k8 : Fin 8 := ⟨k, hk8⟩
    constructor
    · rw [show dst + k * 2 = dst + (k8.val * 2) by simp]
      rw [vstore_read dst outLo h ⟨k8.val * 2, by omega⟩]
      rw [unpacklo8_even hiVec loVec k8]
      rw [fHi.correct v ⟨k, hk⟩]
      · simp [v, Fin.castAdd]
      · exact hpreHi ⟨k, hk⟩
    · rw [show dst + k * 2 + 1 = dst + (k8.val * 2 + 1) by simp]
      rw [vstore_read dst outLo h ⟨k8.val * 2 + 1, by omega⟩]
      rw [unpacklo8_odd hiVec loVec k8]
      rw [fLo.correct v ⟨k, hk⟩]
      · simp [v, Fin.castAdd]
      · exact hpreLo ⟨k, hk⟩
  · -- k ∈ {8,..,15}: bytes come from outHi stored at dst+16
    have hk8' : 8 ≤ k := by omega
    let j : Fin 8 := ⟨k - 8, by omega⟩
    have hjk : j.val + 8 = k := by simp [j]; omega
    -- dst+k*2 = dst+16 + j*2
    have haddr_hi : dst + k * 2 = (dst + 16) + j.val * 2 := by simp [j]; omega
    have haddr_lo : dst + k * 2 + 1 = (dst + 16) + j.val * 2 + 1 := by simp [j]; omega
    -- The inner vstore (at dst) is a frame for these addresses
    have hfrm_hi : ¬ (dst ≤ dst + k * 2 ∧ dst + k * 2 < dst + 16) := by omega
    have hfrm_lo : ¬ (dst ≤ dst + k * 2 + 1 ∧ dst + k * 2 + 1 < dst + 16) := by omega
    constructor
    · rw [haddr_hi]
      rw [vstore_read (dst + 16) outHi h1 ⟨j.val * 2, by omega⟩]
      rw [unpackhi8_even hiVec loVec j]
      rw [fHi.correct v ⟨k, hk⟩]
      · simp [v]; congr 1; omega
      · exact hpreHi ⟨k, hk⟩
    · rw [haddr_lo]
      rw [vstore_read (dst + 16) outHi h1 ⟨j.val * 2 + 1, by omega⟩]
      rw [unpackhi8_odd hiVec loVec j]
      rw [fLo.correct v ⟨k, hk⟩]
      · simp [v]; congr 1; omega
      · exact hpreLo ⟨k, hk⟩

end RightByte
