import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Commons.Analysis.Complex

lemma one_sub_exp_ne_zero_of_mem_Ioo {x : ℝ} (hxlo : -2 * Real.pi < x)
    (hxhi : x < 2 * Real.pi) (hx0 : x ≠ 0) :
    1 - Complex.exp (x * Complex.I) ≠ 0 := by
  intro h
  have hExp : Complex.exp (x * Complex.I) = 1 := (sub_eq_zero.mp h).symm
  have hcos : Real.cos x = 1 := by
    simpa using congrArg Complex.re hExp
  have hxlo' : -(2 * Real.pi) < x := by simpa [neg_mul] using hxlo
  have hx_eq : x = 0 := (Real.cos_eq_one_iff_of_lt_of_lt hxlo' hxhi).mp hcos
  exact hx0 hx_eq

end Commons.Analysis.Complex