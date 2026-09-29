import Mathlib
import Submission.Work.Haupt.thetaCore
import Submission.Work.Haupt.Phi_differentiableOn

/-!
# Holomorphy of `ThetaSum x` on `ℂ \ {0}`

`ThetaSum x z = ∑' n : ℤ, x ^ (n^2) * z^n` is, by definition, the same two-sided theta
series as `jtpTheta x z = Phi x z` from the Jacobi-triple-product development, where the
holomorphy claim on `ℂ \ {0}` (for `‖x‖ < 1`) is proved as `Work.Haupt.Phi_differentiableOn`
(domination on a small ball around each `z ≠ 0` by `‖x‖^(n^2) * R^{|n|}` and Weierstrass'
theorem `Complex.differentiableOn_tsum_of_summable_norm`).

Here we record that statement under the name requested for the `HauptFacts` area of the
CDT project, so that it applies verbatim to `ThetaSum`.
-/

namespace Work.Haupt

noncomputable section

/-- `ThetaSum x` agrees with the two-sided theta series `Phi x = jtpTheta x` used in the
Jacobi triple product development. -/
theorem ThetaSum_eq_Phi (x : ℂ) : ThetaSum x = Phi x := rfl

theorem ThetaSum_analytic (x : ℂ) (hx : ‖x‖ < 1) :
    DifferentiableOn ℂ (ThetaSum x) {z : ℂ | z ≠ 0} := by
  rw [ThetaSum_eq_Phi]
  exact Phi_differentiableOn x hx

end

end Work.Haupt
