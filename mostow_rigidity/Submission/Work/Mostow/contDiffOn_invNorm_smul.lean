import Mathlib

namespace Work.Mostow

open scoped RealInnerProductSpace

/-- The map `y ↦ ‖y‖⁻¹ • y` is `C¹` on the region where `‖y‖ > c`, for any `c > 0`.
It is the composition of scalar inversion of the (smooth away from `0`) norm function
with the identity, using that the region forces `y ≠ 0`. -/
theorem contDiffOn_invNorm_smul {n : ℕ} {c : ℝ} (hc : 0 < c) :
    ContDiffOn ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) => (‖y‖)⁻¹ • y) {y | c < ‖y‖} := by
  have hnorm : ContDiffOn ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) {y | c < ‖y‖} :=
    (contDiffOn_id (𝕜 := ℝ)).norm ℝ (fun x hx => by
      have hx' : c < ‖x‖ := hx
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hc hx'.le)))
  exact (hnorm.inv (fun x hx => by
      have hx' : c < ‖x‖ := hx
      exact ne_of_gt (lt_of_lt_of_le hc hx'.le))).smul
    (contDiffOn_id (𝕜 := ℝ))

end Work.Mostow
