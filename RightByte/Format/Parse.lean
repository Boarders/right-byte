import RightByte.Format.Basic

namespace RightByte

/-- Look up a tag in a `TagTable`. -/
def TagTable.find (eq : τ.Ty → τ.Ty → Bool) (tag : τ.Ty) : TagTable τ υ → Option (Format υ)
  | .done          => none
  | .default f     => some f
  | .cons t f rest => if eq t tag then some f else TagTable.find eq tag rest

/--
Various helpers for constructing primitive types from bytes
Used when parsing bytes
-/
def mk_le_u16 (bytes : UInt8 × UInt8) : UInt16 :=
  match bytes with
  | (l_b, h_b) => h_b.toUInt16 <<< 8 ||| l_b.toUInt16

def mk_le_u32 (bytes : UInt8 × UInt8 × UInt8 × UInt8) : UInt32 :=
  match bytes with
  | (ll_b, lh_b, hl_b, hh_b) =>
    hh_b.toUInt32 <<< 24 |||
    hl_b.toUInt32 <<< 16 |||
    lh_b.toUInt32 <<< 8  |||
    ll_b.toUInt32

def mk_be_u32 (bytes : UInt8 × UInt8 × UInt8 × UInt8) : UInt32 :=
  match bytes with
  | (hh_b, hl_b, lh_b, ll_b) =>
    hh_b.toUInt32 <<< 24 |||
    hl_b.toUInt32 <<< 16 |||
    lh_b.toUInt32 <<< 8  |||
    ll_b.toUInt32

def mk_le_u64 (bytes : UInt8 × UInt8 × UInt8 × UInt8 × UInt8 × UInt8 × UInt8 × UInt8) : UInt64 :=
  match bytes with
  | (b0, b1, b2, b3, b4, b5, b6, b7) =>
    b7.toUInt64 <<< 56 ||| b6.toUInt64 <<< 48 ||| b5.toUInt64 <<< 40 ||| b4.toUInt64 <<< 32 |||
    b3.toUInt64 <<< 24 ||| b2.toUInt64 <<< 16 ||| b1.toUInt64 <<< 8  ||| b0.toUInt64


/-- Read elements from bytearray at offset off of length len into a Nat -/
def readBytesAsNat (buf : ByteArray) (off len : Nat) : Nat :=
  (List.range len).foldl (fun acc i => acc ||| (buf[off + i]!.toNat <<< (8 * i))) 0

mutual
/-- Parse a value of type `τ.Ty` from `buf` starting at byte offset `off`.

    Note/TODO: This function is `partial` as a `tagUnion` recurses into formats
    retrieved from a `TagTable`, which we need to separately prove are structurally
    smaller. -/
partial def Format.parse : Format τ → ByteArray → Nat → Option (τ.Ty × Nat)
  | .u8,                    buf, off =>
      if off < buf.size then some (buf[off]!, off + 1) else none
  | .u16le,                 buf, off =>
      if off + 2 ≤ buf.size then
        some (mk_le_u16 ⟨buf[off]!, buf[off + 1]!⟩, off + 2)
      else
        none
  | .u32le,                 buf, off =>
      if off + 4 ≤ buf.size then
        some (mk_le_u32 ⟨buf[off]!, buf[off + 1]!, buf[off + 2]!, buf[off + 3]!⟩, off + 4)
      else
        none
  | .u32be,                 buf, off =>
      if off + 4 ≤ buf.size then
        some (mk_be_u32 ⟨buf[off]!, buf[off + 1]!, buf[off + 2]!, buf[off + 3]!⟩, off + 4)
      else
        none
  | .u64le,                 buf, off =>
      if off + 8 ≤ buf.size then
        some (mk_le_u64 ⟨buf[off]!, buf[off + 1]!, buf[off + 2]!, buf[off + 3]!,
                         buf[off + 4]!, buf[off + 5]!, buf[off + 6]!, buf[off + 7]!⟩, off + 8)
      else
        none
  | .bits n,                buf, off =>
      let byteCount := (n + 7)/8
      if off + byteCount <= buf.size then
        some (BitVec.ofNat n (readBytesAsNat buf off byteCount), off + byteCount)
      else
        none
  | .seq f g,               buf, off => do
    let (f_val, off') <- f.parse buf off
    let (g_val, off'') <- g.parse buf off'
    pure ((f_val, g_val), off'')
  | .rep n f,               buf, off => parseN f buf n off
  | .aligned n f,           buf, off =>
    let aligned := off + (n - off % n) % n
    f.parse buf aligned
  | .lengthPrefixed lenF f, buf, off => do
    let (len, off') <- lenF.parse buf off
    let subBuf := buf.extract off' (off' + len.toNat)
    let (val, _) ← f.parse subBuf 0
    pure (val, off' + len.toNat)
  | .countPrefixed lenF f,  buf, off => do
    let (rep, off') <- lenF.parse buf off
    let (⟨arr, _⟩, off'') <- parseN f buf rep.toNat off'
    pure (arr, off'')
  | .tagUnion eq tagF table, buf, off => do
     let (tag, off') <- tagF.parse buf off
     match table.find eq tag with
     | none        => none
     | some format =>
         let (val, off'') <- format.parse buf off'
         pure ((tag, val), off'')

partial def parseN (f : Format τ) (buf : ByteArray) : (n : Nat) → Nat → Option (Vector τ.Ty n × Nat)
    | 0,     off => some (⟨#[], rfl⟩, off)
    | n + 1, off => do
        let (xs, off')  ← parseN f buf n off
        let (x,  off'') ← f.parse buf off'
        pure (xs.push x, off'')
end

end RightByte
