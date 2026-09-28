import Mathlib

namespace Work.HP.BCS

/-- Cauchy–Schwarz: if `c * ‖t‖ < |⟪a,t⟫|` then `c < ‖a‖`.

Indeed `|⟪a,t⟫| ≤ ‖a‖ ‖t‖`, so `c ‖t‖ < ‖a‖ ‖t‖`; dividing by the
nonnegative factor `‖t‖` (the case `‖t‖ = 0` is vacuous) gives `c < ‖a‖`. -/
theorem lt_norm_of_lt_abs_inner {k : ℕ} (a : EuclideanSpace ℝ (Fin k)) (c : ℝ)
    {t : EuclideanSpace ℝ (Fin k)} (h : c * ‖t‖ < |inner ℝ a t|) : c < ‖a‖ := by
  refine lt_of_mul_lt_mul_right ?_ (norm_nonneg t)
  exact lt_of_lt_of_le h (abs_real_inner_le_norm a t)

end Work.HP.BCS
