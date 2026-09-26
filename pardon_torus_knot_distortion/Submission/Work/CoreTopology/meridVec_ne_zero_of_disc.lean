import Mathlib
import Submission.Work.CoreTopology.TorusDichotomyDefs
import Submission.Work.CoreTopology.meridVec_torusMap_div_norm

open LeanEval.KnotTheory.PardonDistortion

namespace Work.CoreTopology

noncomputable section

/-- If the meridian projection of a point of `ℝ³` vanishes then the point lies on the core
circle of the solid torus, i.e. its height is `0`. -/
theorem torusHeight_eq_zero_of_meridVec_eq_zero {P : R3} (h : meridVec P = 0) :
    torusHeight P = 0 := by
  obtain ⟨h1, h2⟩ := (meridVec_eq_zero_iff P).mp h
  rw [torusHeight_apply, h1, h2]
  norm_num

/-- **A compressing disc whose interior lies outside the torus misses the meridian circle.**  Let
`α` be a closed curve on the standard torus and let `e : 𝔻 → ℝ³` be a map whose restriction to the
boundary circle is `α` (`e (circlePoint θ) = α.γ θ`).  If every point of the open unit disc is
mapped strictly outside the solid torus bounded by the torus, `1 < torusHeight (e z)`, then the
meridian projection `(r - 2, z)` of `e z` never vanishes on the whole closed disc. -/
theorem meridVec_ne_zero_of_disc (α : Work.CoreTopology.ClosedCurve Work.CoreTopology.standard)
    (e : C(Metric.closedBall (0 : ℂ) 1, LeanEval.KnotTheory.PardonDistortion.R3))
    (hbd : ∀ θ : ℝ, e (Work.CoreTopology.circlePoint θ) = α.γ θ)
    (h_out : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 →
      1 < Work.CoreTopology.torusHeight (e z)) :
    ∀ z : Metric.closedBall (0 : ℂ) 1, Work.CoreTopology.meridVec (e z) ≠ 0 := by
  intro z
  have hle : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- interior: the height is `> 1`, whereas a vanishing meridian projection forces height `0`
    intro hzero
    have hgt := h_out z hlt
    have h0 := torusHeight_eq_zero_of_meridVec_eq_zero hzero
    linarith
  · -- boundary: `z = circlePoint θ` and `e z = α.γ θ` lies on the standard torus, where the
    -- meridian projection is `exp (i φ) ≠ 0`
    obtain ⟨θ, hθ⟩ := exists_circlePoint_eq (z : ℂ) heq
    have hz : circlePoint θ = z := Subtype.ext hθ
    obtain ⟨x, y, hxy⟩ := (ParamTorus.mem_carrier_iff standard (α.γ θ)).mp (α.mem θ)
    have hval : e z = Work.Core.torusMap x y := by
      rw [← hz, hbd θ]
      exact hxy.symm
    intro hzero
    rw [hval, meridVec_torusMap] at hzero
    exact Complex.exp_ne_zero _ hzero

end

end Work.CoreTopology
