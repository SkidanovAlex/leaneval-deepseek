import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.norm_symm_sub_le
import Submission.Work.MRMT.Found.open_subset_closedBall_of_frontier_subset

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Metric

/-- **Image of the ball of radius `Rd + 2`.**  If a homeomorphism `F` of the plane satisfies
the decay estimate `‖F z - z‖ ≤ Cd / ‖z‖` outside the ball of radius `Rd` (with `Rd ≥ 1`,
`Cd ≥ 0`), then `F` maps the ball of radius `Rd + 2` around the origin into the closed ball
of radius `Rd + 2 + Cd`.

The frontier of `F '' ball 0 (Rd+2)` is `F '' sphere 0 (Rd+2)`; every point of that sphere
has norm `Rd + 2 ≥ Rd`, so the decay hypothesis applies to it, and the frontier is contained
in the closed ball of radius `Rd + 2 + Cd`.  The set `F '' ball 0 (Rd+2)` is open and bounded,
so `open_subset_closedBall_of_frontier_subset` gives the containment. -/
theorem image_ball_zero_subset_closedBall_of_decay {F : ℂ ≃ₜ ℂ} {Cd Rd : ℝ} (hRd : 1 ≤ Rd)
    (hCd : 0 ≤ Cd) (hdec : ∀ z : ℂ, Rd ≤ ‖z‖ → ‖F z - z‖ ≤ Cd / ‖z‖) :
    (F : ℂ → ℂ) '' Metric.ball (0 : ℂ) (Rd + 2) ⊆ Metric.closedBall (0 : ℂ) (Rd + 2 + Cd) := by
  set B : Set ℂ := (F : ℂ → ℂ) '' Metric.ball (0 : ℂ) (Rd + 2) with hB
  have hBopen : IsOpen B := by
    rw [hB]
    exact F.isOpenMap _ Metric.isOpen_ball
  have hBbdd : Bornology.IsBounded B :=
    ((isCompact_closedBall (0 : ℂ) (Rd + 2)).image F.continuous).isBounded.subset
      (Set.image_mono Metric.ball_subset_closedBall)
  have hfr : frontier B ⊆ Metric.closedBall (0 : ℂ) (Rd + 2 + Cd) := by
    intro w hw
    rw [hB] at hw
    rw [← Homeomorph.image_frontier F (Metric.ball (0 : ℂ) (Rd + 2))] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hzsp : z ∈ Metric.sphere (0 : ℂ) (Rd + 2) := Metric.frontier_ball_subset_sphere hz
    have hzn : ‖z‖ = Rd + 2 := by
      rw [Metric.mem_sphere, dist_zero_right] at hzsp
      exact hzsp
    have hzR : Rd ≤ ‖z‖ := by rw [hzn]; linarith
    have hdec' := hdec z hzR
    have hz1 : (1 : ℝ) ≤ ‖z‖ := by rw [hzn]; linarith
    have hdiv : Cd / ‖z‖ ≤ Cd := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖z‖)]
      calc Cd = Cd * 1 := (mul_one Cd).symm
        _ ≤ Cd * ‖z‖ := mul_le_mul_of_nonneg_left hz1 hCd
    rw [Metric.mem_closedBall]
    calc dist (F z) 0 = ‖F z‖ := dist_zero_right _
      _ ≤ ‖F z - z‖ + ‖z‖ := by
          have h := norm_add_le (F z - z) z
          rwa [sub_add_cancel] at h
      _ ≤ Cd / ‖z‖ + ‖z‖ := add_le_add hdec' le_rfl
      _ ≤ Cd + (Rd + 2) := add_le_add hdiv (le_of_eq hzn)
      _ = Rd + 2 + Cd := by ring
  have hsub := open_subset_closedBall_of_frontier_subset hBopen hBbdd hfr
  rwa [hB] at hsub

/-- **Uniform volume bound for the image of a unit ball.**  Let `F : ℂ ≃ₜ ℂ` be a
homeomorphism of the plane which is close to the identity outside the ball of radius `Rd`:
`‖F z - z‖ ≤ Cd / ‖z‖` for `‖z‖ ≥ Rd`, with `Rd ≥ 1` and `Cd ≥ 0`.  Then for every centre
`z₀`, the (Lebesgue) area of `F '' ball z₀ 1` is at most the area of the closed ball of
radius `Rd + 2 + Cd`.

If `‖z₀‖ ≤ Rd + 1` then `ball z₀ 1 ⊆ ball 0 (Rd + 2)`, so `F '' ball z₀ 1` is contained in
`F '' ball 0 (Rd + 2)`, which lies in the closed ball of radius `Rd + 2 + Cd` by
`image_ball_zero_subset_closedBall_of_decay`; the conclusion is immediate.  If `‖z₀‖ > Rd + 1`
then every point of `ball z₀ 1` has norm `> Rd`, so the decay hypothesis bounds the
displacement by `Cd / ‖z‖ ≤ Cd / Rd`, giving `F '' ball z₀ 1 ⊆ closedBall z₀ (1 + Cd/Rd)`;
the closed balls of radius `1 + Cd/Rd ≤ Rd + 2 + Cd` have area at most that of the closed
ball of radius `Rd + 2 + Cd`. -/
theorem fw_volume_image_ball_le {F : ℂ ≃ₜ ℂ} {Cd Rd : ℝ} (hRd : 1 ≤ Rd) (hCd : 0 ≤ Cd)
    (hdec : ∀ z : ℂ, Rd ≤ ‖z‖ → ‖F z - z‖ ≤ Cd / ‖z‖) (z₀ : ℂ) :
    (MeasureTheory.volume ((F : ℂ → ℂ) '' Metric.ball z₀ (1 : ℝ))).toReal
      ≤ (MeasureTheory.volume (Metric.closedBall (0 : ℂ) (Rd + 2 + Cd))).toReal := by
  have hRdpos : (0 : ℝ) < Rd := by linarith
  have hfin : (MeasureTheory.volume (Metric.closedBall (0 : ℂ) (Rd + 2 + Cd))) ≠ ⊤ :=
    (isCompact_closedBall (0 : ℂ) (Rd + 2 + Cd)).measure_lt_top.ne
  refine ENNReal.toReal_mono hfin ?_
  by_cases hz0 : ‖z₀‖ ≤ Rd + 1
  · -- Near the origin: embed everything in the ball of radius `Rd + 2`.
    have hsub := image_ball_zero_subset_closedBall_of_decay hRd hCd hdec
    have hsubball : Metric.ball z₀ (1 : ℝ) ⊆ Metric.ball (0 : ℂ) (Rd + 2) := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      rw [dist_zero_right]
      rw [dist_eq_norm] at hz
      have h1 : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by
        have h := norm_add_le z₀ (z - z₀)
        have heq : z₀ + (z - z₀) = z := by ring
        rwa [heq] at h
      linarith
    have hAB : (F : ℂ → ℂ) '' Metric.ball z₀ (1 : ℝ)
        ⊆ Metric.closedBall (0 : ℂ) (Rd + 2 + Cd) :=
      (Set.image_mono hsubball).trans hsub
    exact MeasureTheory.measure_mono hAB
  · -- Far from the origin: every point of `ball z₀ 1` has norm `> Rd`.
    rw [not_le] at hz0
    have hA : (F : ℂ → ℂ) '' Metric.ball z₀ (1 : ℝ) ⊆ Metric.closedBall z₀ (1 + Cd / Rd) := by
      rintro w ⟨z, hz, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hzR : Rd < ‖z‖ := by
        have h1 : ‖z₀‖ ≤ ‖z - z₀‖ + ‖z‖ := by
          have h := norm_add_le (z₀ - z) z
          rw [sub_add_cancel] at h
          rwa [norm_sub_rev z₀ z] at h
        linarith
      have hdec' := hdec z (le_of_lt hzR)
      have hdiv : Cd / ‖z‖ ≤ Cd / Rd :=
        div_le_div_of_nonneg_left hCd hRdpos (le_of_lt hzR)
      calc ‖F z - z₀‖ ≤ ‖F z - z‖ + ‖z - z₀‖ := by
            have h := dist_triangle (F z) z z₀
            rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h
            exact h
        _ ≤ Cd / ‖z‖ + 1 := by linarith
        _ ≤ Cd / Rd + 1 := by linarith
        _ = 1 + Cd / Rd := by ring
    refine le_trans (MeasureTheory.measure_mono hA) ?_
    rw [Complex.volume_closedBall, Complex.volume_closedBall]
    have hρle : (1 : ℝ) + Cd / Rd ≤ Rd + 2 + Cd := by
      have hdivle : Cd / Rd ≤ Cd := by
        rw [div_le_iff₀ hRdpos]
        calc Cd = Cd * 1 := (mul_one Cd).symm
          _ ≤ Cd * Rd := mul_le_mul_of_nonneg_left hRd hCd
      linarith
    exact mul_le_mul_left
      (pow_le_pow_left₀ (show (0 : ENNReal) ≤ ENNReal.ofReal (1 + Cd / Rd) from bot_le)
        (ENNReal.ofReal_le_ofReal hρle) 2)
      (↑NNReal.pi : ENNReal)

end Work.MRMT.Found
