import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.riesz_thorin_vec_defs

namespace Work.BourgainPlan.IonescuWainger

/-- **Normalisation of an `ℓ^p`-function.**  For `p > 0` and a nonzero `ℓ^p`-norm of
`f : α → ℂ` (finite `α`), scaling `f` by the inverse of its `ℓ^p`-norm produces a function of
`ℓ^p`-norm exactly `1`:
`∑ a, ‖((∑ a, ‖f a‖^p)^{1/p} : ℂ)⁻¹ * f a‖ ^ p = 1`.
(The hypothesis `0 < ∑ a, ‖f a‖^p` makes the scalar nonzero so that all the `rpow` rearrangements
are valid; the proof is `‖c * f a‖ = c * ‖f a‖` with `c = (∑ ‖f a‖^p)^{-1/p}`, then
`Real.mul_rpow` and `(c^p) = (∑ ‖f a‖^p)^{-1}`.) -/
theorem normalize_lp {α : Type*} [Fintype α] {p : ℝ} (hp : 0 < p) (f : α → ℂ)
    (hf : 0 < ∑ a, ‖f a‖ ^ p) :
    (∑ a, ‖(((((∑ a, ‖f a‖ ^ p) ^ (1 / p) : ℝ)) : ℂ))⁻¹ * f a‖ ^ p) = 1 := by
  have hSnonneg : 0 ≤ ∑ a, ‖f a‖ ^ p := le_of_lt hf
  have hSpowpos : 0 < (∑ a, ‖f a‖ ^ p) ^ (1 / p) := Real.rpow_pos_of_pos hf _
  have hterm : ∀ a, ‖(((((∑ a, ‖f a‖ ^ p) ^ (1 / p) : ℝ)) : ℂ))⁻¹ * f a‖ ^ p
      = (∑ a, ‖f a‖ ^ p)⁻¹ * ‖f a‖ ^ p := by
    intro a
    have hc : ‖((((∑ a, ‖f a‖ ^ p) ^ (1 / p) : ℝ)) : ℂ)‖ = (∑ a, ‖f a‖ ^ p) ^ (1 / p) := by
      rw [show ‖((((∑ a, ‖f a‖ ^ p) ^ (1 / p) : ℝ)) : ℂ)‖
            = |(∑ a, ‖f a‖ ^ p) ^ (1 / p)| from by simp]
      exact abs_of_nonneg (le_of_lt hSpowpos)
    rw [norm_mul, norm_inv, hc]
    rw [← Real.rpow_neg hSnonneg (1 / p)]
    rw [Real.mul_rpow (Real.rpow_nonneg hSnonneg _) (norm_nonneg _)]
    rw [← Real.rpow_mul hSnonneg (-(1 / p)) p]
    have hpmul : -(1 / p) * p = -1 := by
      field_simp
    rw [hpmul, Real.rpow_neg_one]
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [← Finset.mul_sum]
  rw [show (∑ a, ‖f a‖ ^ p)⁻¹ * (∑ a, ‖f a‖ ^ p) = 1 from inv_mul_cancel₀ (ne_of_gt hf)]

end Work.BourgainPlan.IonescuWainger
