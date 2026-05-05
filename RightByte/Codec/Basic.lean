import RightByte.Format.Parse

namespace RightByte

/-- A `Codec α τ` witnesses that values of type `α` can be faithfully encoded
    as wire values of type `τ.Ty` under `fmt`, with `fromRaw` inverse to `toRaw`. -/
structure Codec (α : Type) (τ : FormatTy) where
  fmt       : Format τ
  toRaw     : α → τ.Ty
  fromRaw   : τ.Ty → Option α
  roundtrip : ∀ x, fromRaw (toRaw x) = some x

/-- Parse by running the wire format then lifting through `fromRaw`. -/
def Codec.parse (c : Codec α τ) (buf : ByteArray) (off : Nat) : Option (α × Nat) := do
  let (raw, off') ← c.fmt.parse buf off
  let val ← c.fromRaw raw
  pure (val, off')

end RightByte
