import Mathlib

/-!
# Analyticity of the divided slope

If `φ` is complex differentiable on the unit disc and `φ 0 = 0`, then `dslope φ 0` — the quotient
`z ↦ φ z / z` extended by `φ'(0)` at the origin — is analytic on the unit disc, and
`φ z = z * dslope φ 0 z` for every `z`.

Analyticity is the removable-singularity statement `Complex.differentiableOn_dslope`, and the
factorisation is `sub_smul_dslope_of_zero` in the case `a = 0`.
-/

open scoped Topology
open Filter

namespace Work.Holonomy3

theorem dslope_analytic_factor (φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 1)) (h0 : φ 0 = 0) :
    AnalyticOnNhd ℂ (dslope φ 0) (Metric.ball 0 1) ∧ ∀ z : ℂ, φ z = z * dslope φ 0 z := by
  have hmem : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
  have hd : DifferentiableOn ℂ (dslope φ 0) (Metric.ball 0 1) :=
    (Complex.differentiableOn_dslope (f := φ) (c := 0) (s := Metric.ball 0 1) hmem).mpr hφ
  refine ⟨hd.analyticOnNhd Metric.isOpen_ball, fun z => ?_⟩
  have h := sub_smul_dslope_of_zero h0 z
  rw [sub_zero] at h
  rw [← h, smul_eq_mul]

end Work.Holonomy3
