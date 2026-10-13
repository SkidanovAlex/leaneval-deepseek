import Mathlib
import Submission.Work.WilE3.Taylor.Polar.Basic

-- the analyticity hypothesis of the main statement is not needed for the estimate itself
set_option linter.unusedVariables false

namespace Work.WilE3.Taylor.Grad

/-!
  The Fréchet derivative of `Φ : (Fin k → ℝ) → ℝ` at `x` and the coordinate gradient
  `Work.WilE3.Taylor.grad Φ x` satisfy

  `∑ l, (∇Φ x l)² ≤ ‖fderiv ℝ Φ x‖²`.

  The domain `Fin k → ℝ` carries the sup (product) norm, so a continuous linear functional
  `L : (Fin k → ℝ) →L[ℝ] ℝ` is `v ↦ ∑ l, v l * L (Pi.single l 1)` and its operator norm is the
  `ℓ¹`-norm `∑ l, |L (Pi.single l 1)|` of its coefficient vector, attained at the sign vector
  `l ↦ sign (L (Pi.single l 1))`.  Hence with `L = fderiv ℝ Φ x`, whose coefficients are the
  coordinate partials `∇Φ x l = fderiv ℝ Φ x (Pi.single l 1)`,

  `∑ l, (∇Φ x l)² ≤ (∑ l, |∇Φ x l|)² = ‖fderiv ℝ Φ x‖²`,

  the last step being the elementary `∑ a l² ≤ (∑ a l)²` for nonnegative `a`.
-/

/-- The Fréchet derivative of `Φ` at `x`, applied to `v`, is the dot product of `v` with the
coordinate gradient: `fderiv ℝ Φ x v = ∑ l, v l * ∇Φ x l`.  No smoothness of `Φ` is needed; the
statement is a purely linear-algebraic expansion of `v` in the standard basis. -/
theorem fderiv_apply_eq_sum_grad {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (x v : Fin k → ℝ) :
    fderiv ℝ Φ x v = ∑ l : Fin k, v l * Work.WilE3.Taylor.grad Φ x l := by
  conv_lhs => rw [show v = ∑ l, v l • (Pi.single l (1 : ℝ) : Fin k → ℝ) from by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- **The squared gradient norm is bounded by the squared operator norm of the derivative.**
Since `Fin k → ℝ` carries the sup norm, `‖fderiv ℝ Φ x‖ = ∑ l, |∇Φ x l|`, and
`∑ l, a l² ≤ (∑ l, a l)²` for `a ≥ 0`. -/
theorem sumSqGrad_le_norm_fderiv_sq {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {x : Fin k → ℝ}
    (hΦ : AnalyticAt ℝ Φ x) :
    (∑ l : Fin k, (Work.WilE3.Taylor.grad Φ x l) ^ 2) ≤ ‖fderiv ℝ Φ x‖ ^ 2 := by
  classical
  -- the sign vector of the gradient: its `l`-th entry is the sign of `∇Φ x l`
  let v : Fin k → ℝ := fun l => Real.sign (Work.WilE3.Taylor.grad Φ x l)
  have hv_le : ‖v‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    intro l
    rw [Real.norm_eq_abs]
    change |Real.sign (Work.WilE3.Taylor.grad Φ x l)| ≤ 1
    rcases lt_trichotomy (Work.WilE3.Taylor.grad Φ x l) 0 with h | h | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [h, Real.sign_zero]; norm_num
    · rw [Real.sign_of_pos h]; norm_num
  -- the derivative evaluated at the sign vector is the sum of the absolute values
  have hval : fderiv ℝ Φ x v = ∑ l : Fin k, |Work.WilE3.Taylor.grad Φ x l| := by
    rw [fderiv_apply_eq_sum_grad]
    refine Finset.sum_congr rfl fun l _ => ?_
    change Real.sign (Work.WilE3.Taylor.grad Φ x l) * Work.WilE3.Taylor.grad Φ x l
      = |Work.WilE3.Taylor.grad Φ x l|
    rcases lt_trichotomy (Work.WilE3.Taylor.grad Φ x l) 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · rw [h, Real.sign_zero, abs_zero]; ring
    · rw [Real.sign_of_pos h, abs_of_pos h]; ring
  -- hence the `ℓ¹`-norm of the gradient is at most the operator norm
  have hbound : (∑ l : Fin k, |Work.WilE3.Taylor.grad Φ x l|) ≤ ‖fderiv ℝ Φ x‖ := by
    have h1 : |fderiv ℝ Φ x v| ≤ ‖fderiv ℝ Φ x‖ := by
      calc |fderiv ℝ Φ x v| = ‖fderiv ℝ Φ x v‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ Φ x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ Φ x‖ * 1 := by gcongr
        _ = ‖fderiv ℝ Φ x‖ := mul_one _
    rw [hval, abs_of_nonneg (Finset.sum_nonneg fun l _ => abs_nonneg _)] at h1
    exact h1
  -- `∑ a l² ≤ (∑ a l)²` for the nonnegative `a l = |∇Φ x l|`
  calc ∑ l : Fin k, (Work.WilE3.Taylor.grad Φ x l) ^ 2
      = ∑ l : Fin k, |Work.WilE3.Taylor.grad Φ x l| ^ 2 := by
        refine Finset.sum_congr rfl fun l _ => ?_
        exact (sq_abs _).symm
    _ ≤ (∑ l : Fin k, |Work.WilE3.Taylor.grad Φ x l|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun l _ => abs_nonneg _
    _ ≤ ‖fderiv ℝ Φ x‖ ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (Finset.sum_nonneg fun l _ => abs_nonneg _) hbound

end Work.WilE3.Taylor.Grad
