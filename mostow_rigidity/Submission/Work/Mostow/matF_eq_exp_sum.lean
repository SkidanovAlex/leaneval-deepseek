import Mathlib
import Submission.Work.Mostow.LinAlgMatrixIneqAux

/-!
# `matF` as the exponential of the sum of `matG`

`matF y = (∏ √(y i)) / ∏ (1 - y i)` and `matG x = log (√x / (1 - x))`, so on the
box `0 < y i < 1` the product `matF y` is `exp (∑ i, matG (y i))`.
-/

namespace Work.Mostow

/-- Pointwise form of the identity: `exp (matG x) = √x / (1 - x)` on `(0,1)`. -/
theorem exp_matG_eq (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    Real.exp (matG x) = Real.sqrt x / (1 - x) := by
  have h1' : Real.exp ((1 / 2 : ℝ) * Real.log x) = Real.sqrt x := by
    rw [mul_comm, ← Real.rpow_def_of_pos h0 (1 / 2), ← Real.sqrt_eq_rpow]
  have hy : 0 < 1 - x := by linarith
  rw [matG, Real.exp_sub, h1', Real.exp_log hy]

theorem matF_eq_exp_sum {n : ℕ} {y : Fin n → ℝ} (h0 : ∀ i, 0 < y i) (h1 : ∀ i, y i < 1) :
    matF y = Real.exp (∑ i, matG (y i)) := by
  have hterm : ∀ i, Real.exp (matG (y i)) = Real.sqrt (y i) / (1 - y i) :=
    fun i => exp_matG_eq (y i) (h0 i) (h1 i)
  rw [matF, Real.exp_sum]
  rw [Finset.prod_congr rfl (fun i _ => hterm i)]
  rw [Finset.prod_div_distrib]

end Work.Mostow
