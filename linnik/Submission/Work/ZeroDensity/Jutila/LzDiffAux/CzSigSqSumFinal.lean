import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.CzRIAux
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRIIRow4Final

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila

/-- `Σ_{r ≤ M} σ_{-1/2}(r)·r² ≤ 3·M³`, where `σ_{-1/2}(r) = czSig r = Σ_{d ∣ r} d^{-1/2}`.

This is the `y = 1` case of `row4_core_lz`, which bounds the same divisor sum times the
weight `(r/y)²` by `3·R³/y²`; substituting `y = 1` gives the claim. -/
theorem CzSigSqSumFinal :
    ∀ M : ℕ, (∑ r ∈ Finset.Icc 1 M, Work.ZeroDensity.Jutila.BzCross.czSig r * (r : ℝ)^2) ≤ 3 * (M : ℝ)^3 := by
  intro M
  have h := row4_core_lz M (y := 1) (by norm_num)
  simpa [Work.ZeroDensity.Jutila.BzCross.czSig] using h

end Work.ZeroDensity.Jutila.LzDiffAux
