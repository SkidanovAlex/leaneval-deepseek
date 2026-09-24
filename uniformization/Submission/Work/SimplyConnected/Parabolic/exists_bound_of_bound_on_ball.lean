import Mathlib
import Submission.Work.SimplyConnected.Parabolic.PlanarEstimates

namespace Work.SimplyConnected.Parabolic

open scoped Topology
open Metric Set

noncomputable section

/-- **Local boundedness of normalised univalent functions.**

Given a universal growth bound `‖F z‖ + 1 ≤ ((1+‖z‖)/(1-‖z‖))^C` for univalent `F` on the unit
disc with `F 0 = 0`, `F' 0 = 1` (hypothesis `hgrowth`), any function `f` which is analytic and
injective on the disc `ball a R` with `deriv f a ≠ 0` and which is bounded by `M` on the smaller
disc `ball a s` (`s < R`) is bounded by `M * K` on the disc `ball a (R/2)`.

The proof rescales `f` about `a` to a normalised univalent function on the unit disc and applies
`norm_sub_le_of_growth`; the derivative `deriv f a` appearing in that estimate is controlled by
the Schwarz lemma (Cauchy's estimate) from the bound `M` on `ball a s`. -/
theorem exists_bound_of_bound_on_ball {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
      Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
      ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ + 1 ≤ ((1 + ‖z‖) / (1 - ‖z‖)) ^ C)
    {a : ℂ} {R s M : ℝ} (hR : 0 < R) (hs : 0 < s) (hsR : s < R) (hM0 : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {f : ℂ → ℂ},
      (∀ z ∈ Metric.ball a R, AnalyticAt ℂ f z) →
      Set.InjOn f (Metric.ball a R) → deriv f a ≠ 0 →
      (∀ z ∈ Metric.ball a s, ‖f z‖ ≤ M) →
      ∀ z ∈ Metric.ball a (R / 2), ‖f z‖ ≤ M * K := by
  refine ⟨1 + 2 * R / s * ((3 : ℝ) ^ C - 1), ?_, ?_⟩
  · have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ C := Real.one_le_rpow (by norm_num) hC.le
    have h3' : 0 ≤ (3 : ℝ) ^ C - 1 := by linarith
    have hRs : 0 ≤ 2 * R / s := div_nonneg (by linarith) hs.le
    nlinarith [mul_nonneg hRs h3']
  · intro f han hinj hder hbnd z hz
    have hsub : Metric.ball a s ⊆ Metric.ball a R := Metric.ball_subset_ball hsR.le
    have hzR : z ∈ Metric.ball a R := Metric.ball_subset_ball (by linarith) hz
    have hdiff : DifferentiableOn ℂ f (Metric.ball a s) := fun w hw =>
      ((han w (hsub hw)).differentiableAt).differentiableWithinAt
    have hfa : ‖f a‖ ≤ M := hbnd a (Metric.mem_ball_self hs)
    have hmaps : Set.MapsTo f (Metric.ball a s) (Metric.closedBall (f a) (2 * M)) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hw' : ‖f w‖ ≤ M := hbnd w hw
      calc ‖f w - f a‖ ≤ ‖f w‖ + ‖f a‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add hw' hfa
        _ = 2 * M := by ring
    have hder' : ‖deriv f a‖ ≤ 2 * M / s :=
      Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmaps hs
    have hgr := norm_sub_le_of_growth hC hgrowth hR han hinj hder z hzR
    have hza : ‖z - a‖ < R / 2 := by
      have := hz
      rw [Metric.mem_ball, dist_eq_norm] at this
      exact this
    have ht0 : 0 ≤ ‖z - a‖ / R := div_nonneg (norm_nonneg _) hR.le
    have ht : ‖z - a‖ / R ≤ 1 / 2 := by
      rw [div_le_iff₀ hR]
      linarith
    have ht1 : ‖z - a‖ / R < 1 := by linarith
    have hmono := growthFun_mono hC ht0 ht (by norm_num : (1 : ℝ) / 2 < 1)
    have hgf : growthFun C (1 / 2) = (3 : ℝ) ^ C - 1 := by
      rw [growthFun]
      norm_num
    have hgnn : 0 ≤ growthFun C (‖z - a‖ / R) := growthFun_nonneg hC ht0 ht1
    have hB : growthFun C (‖z - a‖ / R) ≤ (3 : ℝ) ^ C - 1 := by
      rw [← hgf]; exact hmono
    have hbpos : 0 ≤ R * (2 * M / s) :=
      mul_nonneg hR.le (div_nonneg (by linarith) hs.le)
    have hstep : R * ‖deriv f a‖ * growthFun C (‖z - a‖ / R)
        ≤ R * (2 * M / s) * ((3 : ℝ) ^ C - 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hder' hR.le) hB hgnn hbpos
    have hmain : ‖f z - f a‖ ≤ R * (2 * M / s) * ((3 : ℝ) ^ C - 1) := le_trans hgr hstep
    calc ‖f z‖ = ‖(f z - f a) + f a‖ := by rw [sub_add_cancel]
      _ ≤ ‖f z - f a‖ + ‖f a‖ := norm_add_le _ _
      _ ≤ R * (2 * M / s) * ((3 : ℝ) ^ C - 1) + M := add_le_add hmain hfa
      _ = M * (1 + 2 * R / s * ((3 : ℝ) ^ C - 1)) := by ring

end

end Work.SimplyConnected.Parabolic
