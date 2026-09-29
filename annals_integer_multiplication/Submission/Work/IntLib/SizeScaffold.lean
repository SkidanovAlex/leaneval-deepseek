import Mathlib
import Submission.Work.IntLib.SizeShared
import Submission.Work.IntLib.SizeCount
import Submission.Work.IntLib.SizeEmit
import Submission.Work.IntLib.sizeHalvePiece
import Submission.Work.IntLib.sizeBinUnaryPiece
import Submission.Work.IntLib.decValuePiece

/-!
# The six low-level pieces of `size` / `clog 2` / `pow2`

Interface for `Submission/Work/IntLib/sizeWord.lean`: the three low-level pieces that are
currently delegated.  (`sizeCountPiece`, `sizeEmit`, `sizeEmitZeros` are proved in
`SizeCount.lean` / `SizeEmit.lean`.)
-/

set_option autoImplicit false

namespace Work.IntLib
namespace Size

open HvdH

/-- **Piece `sizeHalve`.** Repeatedly halve the unary counter `u` on stack 1, pushing the parity
bits (least significant first) onto stack 3.  At the end the counter is empty, stack 2 (the
halving scratch) is restored, and stack 3 is `(u.bits).reverse.map bit` above a fresh marker
`gC`.  Cost `O(u)`. -/
theorem sizeHalve : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (u : ℕ)
    (below1 below2 below3 : List Glyph) (s : State),
  s.stk 1 = toks u ++ gA :: below1 → s.stk 2 = below2 → s.stk 3 = below3 →
  ∃ (s' : State) (c : ℕ), Eval main prog s s' c ∧ c ≤ K * (u + 1) ∧
    s'.stk 1 = gA :: below1 ∧ s'.stk 2 = below2 ∧
    s'.stk 3 = (u.bits).reverse.map Glyph.bit ++ gC :: below3 ∧
    ∀ k : Stk, k ≠ 1 → k ≠ 2 → k ≠ 3 → s'.stk k = s.stk k := sizeHalvePiece

/-- **Piece `sizeBinUnary`.** Read the binary expansion of `n` (after an arbitrary sign glyph,
above the closing `iend`) off stack 0 and build the unary counter `n` on stack 1 (marker `gA`).
Cost `O(n + n.size)`. -/
theorem sizeBinUnary : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (n : ℕ) (sg : Glyph)
    (below0 below1 : List Glyph) (s : State),
  s.stk 0 = sg :: (Computability.encodeNat n).map Glyph.bit ++ [Glyph.iend] ++ below0 →
  s.stk 1 = below1 →
  ∃ (s' : State) (c : ℕ), Eval main prog s s' c ∧ c ≤ K * (n + n.size + 1) ∧
    s'.stk 0 = below0 ∧ s'.stk 1 = toks n ++ gA :: below1 ∧
    ∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k := sizeBinUnaryPiece

/-- **Piece `decValue`.** Subtract one from a positive integer value on top of the value stack.
Cost `O(isz)`. -/
theorem decValue : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd), WordR main prog
  (fun vs => ∃ (n : ℕ) (rest : List Val), vs = .int (n + 1) :: rest)
  (fun vs out => ∃ (n : ℕ) (rest : List Val), vs = .int (n + 1) :: rest ∧ out = .int n :: rest)
  (fun vs => K * (vsz (vs.headD .nil) + 1)) := decValuePiece

end Size
end Work.IntLib
