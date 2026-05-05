import Mathlib.Data.Finmap

namespace RightByte

/-- Flat byte-addressed memory: a finite partial map from addresses to bytes.
    Addresses not present in the map read as 0. -/
abbrev Heap := Finmap (fun _ : Nat => UInt8)

def Heap.read (h : Heap) (addr : Nat) : UInt8 :=
  (h.lookup addr).getD 0

def Heap.write (h : Heap) (addr : Nat) (val : UInt8) : Heap :=
  h.insert addr val

end RightByte
