import Mathlib
import Submission.Work.FatouL1.normOneSubMulDerivLe
import Submission.Work.Fatou.Analysis.norm_sub_sub_mul_deriv_le

namespace Work.Pert.PinLogDev

/-!
# A second-order Taylor estimate on a small disc

`taylor_two`: a function holomorphic on `Metric.ball 0 r` (`r > 0`) satisfies a quadratic
Taylor estimate `‖u t - u 0 - (deriv u 0) * t‖ ≤ M ‖t‖ ^ 2` on a sufficiently small disc
`‖t‖ ≤ θ`.

The proof is the standard one and uses no explicit Cauchy integral.  Holomorphy on the disc
gives analyticity there (`DifferentiableOn.analyticOnNhd`), hence `deriv (deriv u)` is analytic,
hence continuous, on the disc; on the compact disc of radius `r / 4` it is bounded by some `C`.
The workspace lemma `Work.Fatou.Analysis.norm_sub_sub_mul_deriv_le` then gives, for each `t` with
`‖t‖ ≤ r / 4`, the segmentwise second-order Taylor estimate

  `‖u (0 + t) - u 0 - t * deriv u 0‖ ≤ M * ‖t‖ ^ 2`  with `M = |C| + 1`,

whose second-derivative bound hypothesis holds because the segment from `0` to `t` stays in
`closedBall 0 (r / 4) ⊆ ball 0 r`.

The hypothesis `hu2` (a uniform bound `2`) is not needed for the argument; any holomorphic
function on a disc satisfies the estimate.
-/
set_option linter.unusedVariables false in
theorem taylor_two {u : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) r))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) r, ‖u z‖ ≤ 2) :
    ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧ ∀ t : ℂ, ‖t‖ ≤ θ →
      ‖u t - u 0 - deriv u 0 * t‖ ≤ M * ‖t‖ ^ 2 := by
  -- the working disc
  set ρ : ℝ := r / 4 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hsub : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) r := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_ball, dist_zero_right, hρ] at *
    linarith
  -- analyticity on the disc
  have hAn : AnalyticOnNhd ℂ u (Metric.ball (0 : ℂ) r) := hu.analyticOnNhd Metric.isOpen_ball
  have h2An : AnalyticOnNhd ℂ (deriv (deriv u)) (Metric.ball (0 : ℂ) r) := hAn.deriv.deriv
  have hcont : ContinuousOn (deriv (deriv u)) (Metric.closedBall (0 : ℂ) ρ) :=
    h2An.analyticOn.continuousOn.mono hsub
  -- bound of the second derivative on the compact disc
  obtain ⟨C, hC⟩ :=
    (ProperSpace.isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn hcont
  have hMpos : 0 < |C| + 1 := by have := abs_nonneg C; linarith
  refine ⟨|C| + 1, ρ, hMpos, hρpos, ?_⟩
  intro t ht
  -- the segment `[0, t]` lies in the disc `closedBall 0 ρ`
  have hsegmem : ∀ w ∈ segment ℝ (0 : ℂ) (0 + t), w ∈ Metric.closedBall (0 : ℂ) ρ := by
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨θ, hθ, rfl⟩ := hw
    have hβ : (fun θ => 0 + θ • (0 + t - 0)) θ = θ • t := by simp
    rw [Metric.mem_closedBall, dist_zero_right, hβ, norm_smul, Real.norm_of_nonneg hθ.1]
    calc θ * ‖t‖ ≤ 1 * ‖t‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg t)
      _ = ‖t‖ := one_mul _
      _ ≤ ρ := ht
  have hseg : ∀ w ∈ segment ℝ (0 : ℂ) (0 + t), AnalyticAt ℂ u w :=
    fun w hw => hAn w (hsub (hsegmem w hw))
  have hb : ∀ w ∈ segment ℝ (0 : ℂ) (0 + t), ‖deriv (deriv u) w‖ ≤ |C| + 1 :=
    fun w hw => by linarith [hC w (hsegmem w hw), le_abs_self C]
  have hmain := Work.Fatou.Analysis.norm_sub_sub_mul_deriv_le (f := u) (z := 0) (a := t)
    (M := |C| + 1) hseg hb
  rw [zero_add, mul_comm t (deriv u 0)] at hmain
  exact hmain

end Work.Pert.PinLogDev
