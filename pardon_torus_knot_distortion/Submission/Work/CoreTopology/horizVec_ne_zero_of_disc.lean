import Mathlib
import Submission.Work.CoreTopology.TorusDichotomyDefs
import Submission.Work.CoreTopology.meridVec_torusMap_div_norm

open LeanEval.KnotTheory.PardonDistortion

namespace Work.CoreTopology

noncomputable section

/-- The height function takes the value `1` on every point of the standard torus:
`torusHeight (torusMap θ φ) = (2 + cos φ - 2)² + sin²φ = cos²φ + sin²φ = 1`. -/
theorem torusHeight_torusMap (θ φ : ℝ) : torusHeight (Work.Core.torusMap θ φ) = 1 := by
  rw [torusHeight_apply, horizRadius_torusMap, Work.Core.torusMap_apply_two]
  nlinarith [Real.sin_sq_add_cos_sq φ]

/-- Every point of the standard torus has height `1`. -/
theorem torusHeight_eq_one_of_mem_carrier {P : R3} (hP : P ∈ standard.carrier) :
    torusHeight P = 1 := by
  obtain ⟨x, y, hxy⟩ := (ParamTorus.mem_carrier_iff standard P).mp hP
  rw [← hxy, standard_psi, torusHeight_torusMap]

/-- On the `z`-axis the height function is at least `4`: if `horizRadius P = 0` then
`torusHeight P = 4 + (P 2)² ≥ 4`. -/
theorem four_le_torusHeight_of_horizRadius_eq_zero {P : R3} (h : horizRadius P = 0) :
    4 ≤ torusHeight P := by
  rw [torusHeight_apply, h]
  nlinarith [sq_nonneg (P 2)]

/-- **A compressing disc whose interior lies inside the solid torus misses the `z`-axis.**  Let
`α` be a closed curve on the standard torus and let `e : 𝔻 → ℝ³` be a map whose restriction to the
boundary circle is `α` (`e (circlePoint θ) = α.γ θ`).  If every point of the open unit disc is
mapped strictly inside the solid torus bounded by the torus, `torusHeight (e z) < 1`, then the
horizontal projection `(x, y)` of `e z` never vanishes on the whole closed disc. -/
theorem horizVec_ne_zero_of_disc (α : Work.CoreTopology.ClosedCurve Work.CoreTopology.standard)
    (e : C(Metric.closedBall (0 : ℂ) 1, LeanEval.KnotTheory.PardonDistortion.R3))
    (hbd : ∀ θ : ℝ, e (Work.CoreTopology.circlePoint θ) = α.γ θ)
    (h_in : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 →
      Work.CoreTopology.torusHeight (e z) < 1) :
    ∀ z : Metric.closedBall (0 : ℂ) 1, Work.CoreTopology.horizVec (e z) ≠ 0 := by
  -- The whole closed disc is mapped into the closed solid torus `{torusHeight ≤ 1}`:
  -- strictly inside on the open disc (hypothesis `h_in`), and onto the torus surface
  -- (where `torusHeight = 1`) on the boundary circle.
  have hle : ∀ z : Metric.closedBall (0 : ℂ) 1, torusHeight (e z) ≤ 1 := by
    intro z
    have hznorm : ‖(z : ℂ)‖ ≤ 1 := by
      have h := z.2
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h
    rcases lt_or_eq_of_le hznorm with hlt | heq
    · exact le_of_lt (h_in z hlt)
    · -- a boundary point of the disc is `circlePoint θ` for some `θ`
      obtain ⟨θ, hθ⟩ := exists_circlePoint_eq (z : ℂ) heq
      have hz : circlePoint θ = z := Subtype.ext hθ
      have heq' : e z = α.γ θ := by rw [← hz]; exact hbd θ
      rw [heq']
      exact le_of_eq (torusHeight_eq_one_of_mem_carrier (α.mem θ))
  intro z hzero
  have hr : horizRadius (e z) = 0 := (horizVec_eq_zero_iff (e z)).mp hzero
  have h4 : 4 ≤ torusHeight (e z) := four_le_torusHeight_of_horizRadius_eq_zero hr
  linarith [hle z]

end

end Work.CoreTopology
