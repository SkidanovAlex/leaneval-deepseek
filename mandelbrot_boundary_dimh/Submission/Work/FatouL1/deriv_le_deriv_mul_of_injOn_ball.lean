import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.Parabolic.PlanarEstimates
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
import Submission.Lib.Unif2.Commons.Analysis.Complex.Landau.landau_theorem
import Submission.Lib.Unif2.Commons.Analysis.Complex.Koebe.weak_koebe_of_landau
import Submission.Lib.Unif2.Commons.Analysis.Complex.Koebe.growth_bound

/-!
# Derivative distortion for injective holomorphic maps on a ball

Koebe-type distortion: there is a universal constant `K` such that for every function `Φ` which is
holomorphic and injective on a ball `ball z₀ R`, the derivative at any point of the concentric half
ball is bounded by `K` times the derivative at the centre.

The proof is the classical one: the Koebe growth bound (Landau's theorem + the weak Koebe
inequality, in the form `Submission...PlanarEstimates.norm_sub_le_of_growth`) shows that `Φ` grows
at most like `R · ‖deriv Φ z₀‖` times a universal function on any smaller concentric ball.  Applying
Cauchy's estimate to `Φ - Φ z` on the quarter ball `ball z (R/4)`, which lies in `ball z₀ R` when
`z` lies in the half ball, converts this into the derivative bound at `z`.
-/

namespace Work.FatouL1

open Metric Set

theorem deriv_le_deriv_mul_of_injOn_ball :
    ∃ K : ℝ, 0 < K ∧ ∀ (Φ : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (z : ℂ), 0 < R →
      (∀ w ∈ Metric.ball z₀ R, AnalyticAt ℂ Φ w) → Set.InjOn Φ (Metric.ball z₀ R) →
      z ∈ Metric.ball z₀ (R / 2) → ‖deriv Φ z‖ ≤ K * ‖deriv Φ z₀‖ := by
  -- The universal normalised growth bound on the unit disc.
  obtain ⟨c₀, hc₀, hlandau⟩ := Commons.Analysis.Complex.Landau.landau_theorem
  have hkoebe := Commons.Analysis.Complex.Koebe.weak_koebe_of_landau hc₀ hlandau
  have hpos : 0 < c₀ / Real.pi := by positivity
  -- The exponent of the universal growth function.
  set c : ℝ := 1 / (c₀ / Real.pi) with hc_def
  have hcpos : 0 < c := by rw [hc_def]; positivity
  have hgrowth : ∀ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
      Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
      ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ + 1 ≤ ((1 + ‖z‖) / (1 - ‖z‖)) ^ c := by
    intro f hf hinj h0 h1
    have := Commons.Analysis.Complex.Koebe.growth_bound hpos hkoebe hf hinj h0 h1
    simpa only [hc_def] using this
  have hgpos : 0 < Work.SimplyConnected.Parabolic.growthFun c (3 / 4) := by
    rw [Work.SimplyConnected.Parabolic.growthFun]
    have h7 : (1 : ℝ) < (1 + 3 / 4) / (1 - 3 / 4) := by norm_num
    have hlt := Real.one_lt_rpow h7 hcpos
    linarith
  refine ⟨8 * Work.SimplyConnected.Parabolic.growthFun c (3 / 4),
    mul_pos (by norm_num) hgpos, ?_⟩
  intro Φ z₀ R z hR hanz hinj hz
  -- Injectivity forces the derivative at the centre to be nonzero.
  have hz0 : z₀ ∈ Metric.ball z₀ R := Metric.mem_ball_self hR
  have hder : deriv Φ z₀ ≠ 0 :=
    Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hR (hanz z₀ hz0) hinj
  -- The scaled growth bound on `ball z₀ R`.
  have hgr := Work.SimplyConnected.Parabolic.norm_sub_le_of_growth (C := c) hcpos hgrowth
    hR hanz hinj hder
  have hd : DifferentiableOn ℂ Φ (Metric.ball z₀ R) :=
    fun w hw => (hanz w hw).differentiableAt.differentiableWithinAt
  have hzlt : dist z z₀ < R / 2 := by simpa [Metric.mem_ball] using hz
  have hsub : Metric.closedBall z (R / 4) ⊆ Metric.ball z₀ R := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖w - z₀‖ = dist w z₀ := by rw [dist_eq_norm]
      _ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ = ‖w - z‖ + dist z z₀ := by rw [dist_eq_norm]
      _ ≤ R / 4 + R / 2 := by linarith
      _ = 3 * R / 4 := by ring
      _ < R := by linarith
  -- The shifted function on the quarter ball.
  let G : ℂ → ℂ := fun w => Φ w - Φ z
  have hGdiff : DifferentiableOn ℂ G (Metric.ball z₀ R) := by
    intro w hw
    have h := (hd w hw).sub (differentiableWithinAt_const (Φ z))
    change DifferentiableWithinAt ℂ (fun w => Φ w - Φ z) (Metric.ball z₀ R) w
    exact h
  have hdG : DiffContOnCl ℂ G (Metric.ball z (R / 4)) := hGdiff.diffContOnCl_ball hsub
  -- Growth bound for points of the quarter ball.
  have hbound_closed (ζ : ℂ) (hζ : ζ ∈ Metric.closedBall z (R / 4)) :
      ‖Φ ζ - Φ z₀‖ ≤ R * ‖deriv Φ z₀‖ * Work.SimplyConnected.Parabolic.growthFun c (3 / 4) := by
    have hdζ : dist ζ z ≤ R / 4 := by simpa [Metric.mem_closedBall] using hζ
    have hζR : ζ ∈ Metric.ball z₀ R := hsub hζ
    have hζn : ‖ζ - z₀‖ ≤ 3 * R / 4 := by
      calc ‖ζ - z₀‖ = dist ζ z₀ := by rw [dist_eq_norm]
        _ ≤ dist ζ z + dist z z₀ := dist_triangle _ _ _
        _ ≤ R / 4 + R / 2 := by linarith
        _ = 3 * R / 4 := by ring
    have ht : ‖ζ - z₀‖ / R ≤ 3 / 4 := by
      rw [div_le_iff₀ hR]
      linarith
    have hmono : Work.SimplyConnected.Parabolic.growthFun c (‖ζ - z₀‖ / R) ≤
        Work.SimplyConnected.Parabolic.growthFun c (3 / 4) :=
      Work.SimplyConnected.Parabolic.growthFun_mono (C := c) hcpos
        (div_nonneg (norm_nonneg _) hR.le) ht (by norm_num : (3 : ℝ) / 4 < 1)
    have hcoef : (0 : ℝ) ≤ R * ‖deriv Φ z₀‖ := mul_nonneg hR.le (norm_nonneg _)
    calc ‖Φ ζ - Φ z₀‖
        ≤ R * ‖deriv Φ z₀‖ * Work.SimplyConnected.Parabolic.growthFun c (‖ζ - z₀‖ / R) :=
          hgr ζ hζR
      _ ≤ R * ‖deriv Φ z₀‖ * Work.SimplyConnected.Parabolic.growthFun c (3 / 4) :=
          mul_le_mul_of_nonneg_left hmono hcoef
  -- On the boundary circle of the quarter ball, `Φ - Φ z` is bounded by the universal constant.
  have hGsph : ∀ ζ ∈ Metric.sphere z (R / 4),
      ‖G ζ‖ ≤ 2 * (R * ‖deriv Φ z₀‖ * Work.SimplyConnected.Parabolic.growthFun c (3 / 4)) := by
    intro ζ hζ
    have hbζ := hbound_closed ζ (Metric.sphere_subset_closedBall hζ)
    have hbz := hbound_closed z (Metric.mem_closedBall_self (by linarith : (0 : ℝ) ≤ R / 4))
    change ‖Φ ζ - Φ z‖ ≤ 2 * (R * ‖deriv Φ z₀‖ * Work.SimplyConnected.Parabolic.growthFun c (3 / 4))
    have harg : Φ ζ - Φ z = (Φ ζ - Φ z₀) - (Φ z - Φ z₀) := by ring
    rw [harg]
    calc ‖(Φ ζ - Φ z₀) - (Φ z - Φ z₀)‖
        ≤ ‖Φ ζ - Φ z₀‖ + ‖Φ z - Φ z₀‖ := norm_sub_le _ _
      _ ≤ R * ‖deriv Φ z₀‖ * Work.SimplyConnected.Parabolic.growthFun c (3 / 4)
            + R * ‖deriv Φ z₀‖ * Work.SimplyConnected.Parabolic.growthFun c (3 / 4) :=
          add_le_add hbζ hbz
      _ = 2 * (R * ‖deriv Φ z₀‖ * Work.SimplyConnected.Parabolic.growthFun c (3 / 4)) := by ring
  -- Cauchy's estimate on the quarter ball.
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := R / 4)
    (C := 2 * (R * ‖deriv Φ z₀‖ * Work.SimplyConnected.Parabolic.growthFun c (3 / 4)))
    (f := G) (by linarith) hdG hGsph
  have hderivG : deriv G z = deriv Φ z := by
    change deriv (fun w => Φ w - Φ z) z = deriv Φ z
    exact deriv_sub_const (f := Φ) (x := z) (Φ z)
  calc ‖deriv Φ z‖ = ‖deriv G z‖ := by rw [hderivG]
    _ ≤ (2 * (R * ‖deriv Φ z₀‖ * Work.SimplyConnected.Parabolic.growthFun c (3 / 4))) / (R / 4) :=
        hcauchy
    _ = 8 * Work.SimplyConnected.Parabolic.growthFun c (3 / 4) * ‖deriv Φ z₀‖ := by
        field_simp [hR.ne']
        ring

end Work.FatouL1
