import RightByte.Mem.Prog
import RightByte.Mem.Symbolic

namespace RightByte

/-- Process a buffer in fixed-size chunks, with a scalar tail for leftovers.

    - `src`, `dst`, `len` are runtime values (addresses and byte count).
    - `inChunk` / `outChunk` are compile-time chunk sizes (e.g. 16 / 32 for base16).
    - `processChunk srcAddr dstAddr` handles one full chunk; receives the
      absolute byte addresses for that chunk.
    - `processTail srcTail dstTail leftover` handles the remaining
      `0..inChunk-1` bytes. -/
def Prog.chunked {var : ProgTy → Type} [Symbolic var]
    (src dst len : var .nat)
    (inChunk outChunk : Nat)
    (processChunk : var .nat → var .nat → Prog var Unit)
    (processTail  : var .nat → var .nat → var .nat → Prog var Unit)
    : Prog var Unit := do
  let nChunks  := Symbolic.divNat len (Symbolic.litNat inChunk)
  let leftover := Symbolic.modNat len (Symbolic.litNat inChunk)
  Prog.forVarN nChunks fun i =>
    processChunk
      (Symbolic.addNat src (Symbolic.mulNat i (Symbolic.litNat inChunk)))
      (Symbolic.addNat dst (Symbolic.mulNat i (Symbolic.litNat outChunk)))
  let srcTail := Symbolic.addNat src (Symbolic.mulNat nChunks (Symbolic.litNat inChunk))
  let dstTail := Symbolic.addNat dst (Symbolic.mulNat nChunks (Symbolic.litNat outChunk))
  processTail srcTail dstTail leftover

end RightByte
