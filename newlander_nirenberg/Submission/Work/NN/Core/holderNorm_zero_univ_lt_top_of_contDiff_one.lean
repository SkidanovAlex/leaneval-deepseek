import Mathlib
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport

namespace Work.NN.Core

/-- A compactly supported `C^1` function on `ℂⁿ` has finite `C^{0,α}` norm on all of `ℂⁿ`,
for every `0 < α < 1`.

This is the `k = 0` case of
`Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport'`: the function is
continuous with compact support, hence bounded, and its gradient is bounded as well,
making the function Lipschitz; a bounded Lipschitz function has bounded divided
differences of every exponent `α ≤ 1`. -/
theorem holderNorm_zero_univ_lt_top_of_contDiff_one {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {W : (Fin n → ℂ) → ℂ} (hW : ContDiff ℝ 1 W) (hWc : HasCompactSupport W) :
    Work.CR.Flat.holderNorm 0 α W Set.univ < ⊤ := by
  have h := Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport'
    (X := Fin n → ℂ) (k := 0) (le_of_lt hα0) (le_of_lt hα1) hW hWc
  exact lt_top_iff_ne_top.mpr h

end Work.NN.Core
