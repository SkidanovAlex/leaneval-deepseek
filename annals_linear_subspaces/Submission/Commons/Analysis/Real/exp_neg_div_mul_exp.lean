import Mathlib.Analysis.Complex.Exponential

namespace Commons.Analysis.Real

lemma exp_neg_div_mul_exp {t ℓ m c : ℝ} (hℓ : ℓ ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) :
    Real.exp (-t / ℓ) / (c * Real.exp (t / m)) = (1 / c) * Real.exp (-t * (1 / ℓ + 1 / m)) := by
  have hE : Real.exp (t / m) ≠ 0 := Real.exp_ne_zero _
  calc
    Real.exp (-t / ℓ) / (c * Real.exp (t / m))
        = (1 / c) * (Real.exp (-t / ℓ) / Real.exp (t / m)) := by
          field_simp [hc, hE]
    _ = (1 / c) * Real.exp (-t / ℓ - t / m) := by
          rw [← Real.exp_sub]
    _ = (1 / c) * Real.exp (-t * (1 / ℓ + 1 / m)) := by
          congr 1
          rw [Real.exp_eq_exp]
          field_simp [hℓ, hm]
          ring

end Commons.Analysis.Real