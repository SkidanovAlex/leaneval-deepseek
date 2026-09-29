import Mathlib
import Submission.Work.SynFFT.kit2

namespace Work.SynFFT

open HvdH

/-!
# `synDFTProp`: the `Fin`-indexed synthetic DFT is the ℕ-indexed one

`HvdH.synDFT` (paper's `G_{t₁,…}`, indexed by `Fin ts.prod`) and `Work.SynFFT.dftMultiN`
(the same operator with natural-number indices, extended by `0` outside `ts.prod`) are the same
function: the two sums are `∑_{k<M}` (`Finset.range`) and `∑_{k : Fin M}` (`Finset.univ`), and on
`k < M` the extension `if h : k < M then u ⟨k,h⟩ else 0` is just `u k`.

This is the bridge that lets the program-level statements about `dftMultiN`
(`AxisIterProp`, `HasAxesFold`) be used for the paper's `synDFT`.
-/

/-- `synDFT` (`Fin`-indexed) is `dftMultiN` (natural-number indexed, with the trivial extension
to `ℕ`). -/
theorem synDFTProp : Work.SynFFT.SynDFTProp := by
  intro r ts sgn u j c
  simp only [synDFT, dftMultiN]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => yMul r (sgn * synExp r ts (digits ts j) (digits ts k))
      (if h : k < ts.prod then u ⟨k, h⟩ else 0) c) ts.prod]
  exact Finset.sum_congr rfl (fun k _ => by simp)

end Work.SynFFT
