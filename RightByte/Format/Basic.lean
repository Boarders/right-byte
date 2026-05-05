namespace RightByte

/-- The closed universe of types that `Format` can parse.
 -/
inductive FormatTy where
  | u8 | u16 | u32 | u64
  | bv   : Nat → FormatTy
  | prod : FormatTy → FormatTy → FormatTy
  | vec  : Nat → FormatTy → FormatTy
  | arr  : FormatTy → FormatTy

/-- Semantic interpretation of `FormatTy` as concrete type. -/
@[reducible] def FormatTy.Ty : FormatTy → Type
  | .u8         => UInt8
  | .u16        => UInt16
  | .u32        => UInt32
  | .u64        => UInt64
  | .bv n       => BitVec n
  | .prod τ υ   => τ.Ty × υ.Ty
  | .vec n τ    => Vector τ.Ty n
  | .arr τ      => Array τ.Ty

mutual

/-- A `Format τ` describes the binary layout of a value of type `τ.Ty`. -/
inductive Format : FormatTy → Type where
  | u8    : Format .u8
  | u16le : Format .u16
  | u32le : Format .u32
  | u32be : Format .u32
  | u64le : Format .u64
  | bits  : (n : Nat) → Format (.bv n)
  | seq   : Format τ → Format υ → Format (.prod τ υ)
  | rep   : (n : Nat) → Format τ → Format (.vec n τ)
  /-- Read format with "n-aligned" memory -/
  | aligned : (n : Nat) → Format τ → Format τ
  /-- Read next N bytes into sub-buffer, where N comes from a preceding length field.
      The inner format describes how to interpret those N bytes. -/
  | lengthPrefixed : Format .u16 → Format τ → Format τ
  /-- Read N items of format `τ`, where N comes from a preceding count field. -/
  | countPrefixed  : Format .u16 → Format τ → Format (.arr τ)
  /-- Tag-dispatched union: parse a tag, look it up in the TagTable.
      This type also includes an explicit equality type that is used
      by the TagTable when doing lookup
  -/
  | tagUnion : (τ.Ty → τ.Ty → Bool) → Format τ → TagTable τ υ → Format (.prod τ υ)

/-- A lookup table mapping tag values to formats, used by `Format.tagUnion`.

    The terminal constructor encodes what happens when no tag matches:
      - `done` is a parse error
      - `default` means fall through to a fixed format
-/
inductive TagTable : FormatTy → FormatTy → Type where
  | done    : TagTable τ υ
  | default : Format υ → TagTable τ υ
  | cons    : τ.Ty → Format υ → TagTable τ υ → TagTable τ υ

end

def TagTable.foldl
    (f    : β → τ.Ty → Format υ → β)
    (term : β → Option (Format υ) → β)
    (init : β) : TagTable τ υ → β
  | .done        => term init none
  | .default d   => term init (some d)
  | .cons t fmt rest => TagTable.foldl f term (f init t fmt) rest

mutual

def Format.staticSize : Format τ → Option Nat
  | .u8                    => some 1
  | .u16le                 => some 2
  | .u32le                 => some 4
  | .u32be                 => some 4
  | .u64le                 => some 8
  | .bits n                => some ((n + 7) / 8)
  | .seq f g               => (· + ·) <$> f.staticSize <*> g.staticSize
  | .rep n f               => (n * ·) <$> f.staticSize
  | .aligned _ f           => f.staticSize
  | .lengthPrefixed _ _    => none
  | .countPrefixed _ _     => none
  | .tagUnion _ f table    => (· + ·) <$> f.staticSize <*> table.uniformSize

def TagTable.uniformSizeGo : Option Nat → TagTable τ υ → Option Nat
  | acc, .done        => acc
  | acc, .default f   =>
      match acc, f.staticSize with
      | none,   sz    => sz
      | some n, some m => if n == m then some n else none
      | some _, none  => none
  | acc, .cons _ fmt rest =>
      let acc' := match acc, fmt.staticSize with
                  | none,   sz    => sz
                  | some n, some m => if n == m then some n else none
                  | some _, none  => none
      TagTable.uniformSizeGo acc' rest

/-- Returns `some n` if every entry and the terminal all agree on static size `n`. -/
def TagTable.uniformSize (table : TagTable τ υ) : Option Nat :=
  TagTable.uniformSizeGo none table

end

/-- A default value for every `FormatTy`-denoted type. -/
def FormatTy.default : (τ : FormatTy) → τ.Ty
  | .u8        => 0
  | .u16       => 0
  | .u32       => 0
  | .u64       => 0
  | .bv _      => 0
  | .prod τ υ  => (FormatTy.default τ, FormatTy.default υ)
  | .vec n τ   => Vector.ofFn (fun _ => FormatTy.default τ)
  | .arr _     => #[]

instance (τ : FormatTy) : Inhabited τ.Ty := ⟨FormatTy.default τ⟩

end RightByte
