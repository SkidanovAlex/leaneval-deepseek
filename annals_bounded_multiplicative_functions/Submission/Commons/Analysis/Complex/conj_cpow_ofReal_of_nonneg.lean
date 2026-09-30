import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Complex

theorem conj_cpow_ofReal_of_nonneg {y : ℝ} (hy : 0 ≤ y) (z : ℂ) :
    (starRingEnd ℂ) (((y : ℝ) : ℂ) ^ z) = ((y : ℝ) : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : (((y : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (((y : ℝ) : ℂ)) z harg
  rw [Complex.conj_ofReal] at h
  exact h.symm

end Commons.Analysis.Complex