import Mathlib
import Submission.Work.Repel.repel3_aux
import Submission.Work.Interfaces.Parabolic

namespace Work.Repel.R3Level0v2

/-- **Target control at an arbitrary radius `R ∈ (r/4, r/2]`.**

This is `Work.Repel.target_control_explicit` applied at radius `2R`: the hypothesis `R ≤ r/2`
gives `closedBall c (4R) ⊆ closedBall c (2r) ⊆ K'` and `closedBall c (2R) ⊆ closedBall c r ⊆ d.Dφ`,
`2R ≤ r` restricts the injectivity of `d.φ` from `ball c r` to `ball c (2R)`, and the smallness
`δ ≤ r‖deriv d.φ c‖/256` combined with `r/4 < R` gives `128δ < (2R)‖deriv d.φ c‖`, which is the
quantitative input of the half-ball lemma.  The conclusion is then stated at radius `2R/2 = R`. -/
theorem target_control_R {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {f : ℂ → ℂ} {Df : Set ℂ} {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ}
    (P : MandelDim.PertData d f Df η y₁ K K' δ)
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hRbig : r / 4 < R) (hRle : R ≤ r / 2)
    (hderiv : deriv d.φ c ≠ 0)
    (hK' : Metric.closedBall c (2 * r) ⊆ K')
    (hsub : Metric.closedBall c r ⊆ d.Dφ)
    (hginj : Set.InjOn d.φ (Metric.ball c r))
    (hδ : δ ≤ r * ‖deriv d.φ c‖ / 256) :
    Set.InjOn P.φ (Metric.ball c R) ∧
      Metric.ball (d.φ c) ((1 / 50 : ℝ) * ‖deriv d.φ c‖ * R - δ) ⊆ P.φ '' Metric.ball c R ∧
      Metric.ball c R ⊆ P.Dφ := by
  have h2R : (0 : ℝ) < 2 * R := by linarith
  -- the compact already contains `closedBall c (2 · (2R))` since `4R ≤ 2r`
  have hK'4 : Metric.closedBall c (2 * (2 * R)) ⊆ K' :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hK'
  -- and `d.φ` is holomorphic on `closedBall c (2R) ⊆ closedBall c r`
  have hsub2R : Metric.closedBall c (2 * R) ⊆ d.Dφ :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hsub
  have hginj2R : Set.InjOn d.φ (Metric.ball c (2 * R)) :=
    hginj.mono (Metric.ball_subset_ball (by linarith))
  have hn : 0 < ‖deriv d.φ c‖ := norm_pos_iff.mpr hderiv
  -- `δ ≤ r‖d.φ' c‖/256` and `r/2 < 2R` give `128δ < (2R)‖d.φ' c‖`
  have hsmall : (128 : ℝ) * δ < (2 * R) * ‖deriv d.φ c‖ := by
    nlinarith [hn, hr, hRbig, hRle, hδ]
  have hmain := Work.Repel.target_control_explicit d P (r := 2 * R)
    h2R hderiv hK'4 hsub2R hginj2R hsmall
  have h2R2 : (2 * R) / 2 = R := by ring
  rw [h2R2] at hmain
  exact hmain

end Work.Repel.R3Level0v2
