import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs

/-!
# The quadratic weight `1 + ε²n²` does not destroy `ℓ²(ℤ)` membership

The weight `w_ε(n) = 1 + ε² n²` is a real number `≥ 1` for every `n : ℤ`, hence
`‖g n‖ ≤ ‖w_ε(n) · g n‖` pointwise.  Consequently, if the weighted sequence `w_ε · g` is
square-summable, so is `g` itself (monotonicity of `Memℓp` under pointwise domination).

This is the elementary "de-weighting" step used when the Ionescu–Wainger multiplier
theorem is applied to a band-limited quadratic weight.
-/

namespace Work.BourgainPlan.IonescuWainger

/-- For every `n : ℤ` and `ε : ℝ` the complex weight `1 + ε² n²` has modulus `≥ 1`
(namely `1 + (ε n)²`, a nonnegative real number `≥ 1`). -/
private lemma one_le_norm_one_add_sq_mul_sq (ε : ℝ) (n : ℤ) :
    (1 : ℝ) ≤ ‖(1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)‖ := by
  have hw : (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2) = ((1 + (ε * (n : ℝ)) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hw, Complex.norm_real, Real.norm_eq_abs]
  exact le_trans (le_add_of_nonneg_right (sq_nonneg (ε * (n : ℝ)))) (le_abs_self _)

theorem memlp_of_mul_quadratic_weight {g : ℤ → ℂ} {ε : ℝ}
    (hW : Memℓp (fun n : ℤ => (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2) * g n) 2) : Memℓp g 2 := by
  refine hW.mono' (fun n => ?_)
  rw [norm_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_norm_one_add_sq_mul_sq ε n)

end Work.BourgainPlan.IonescuWainger
