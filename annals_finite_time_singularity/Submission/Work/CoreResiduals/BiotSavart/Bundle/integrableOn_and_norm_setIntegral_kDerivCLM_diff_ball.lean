import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.CoreResiduals.BiotSavart.integral_kDerivCLM_annulus_eq_zero
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_le
import Submission.Work.CoreResiduals.BiotSavart.integrable_indicator_kDerivCLM_annulus
import Submission.Work.CoreResiduals.BiotSavart.volume_real_ball_three

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.Bundle

open MeasureTheory Metric Set
open scoped Topology NNReal ENNReal

/-! ## Two integrability inputs

The kernel `kDerivCLM` blows up only at the origin.  On any region that stays at a positive
distance `m` from the origin it is dominated by the constant `4/m³` and the region has finite
volume, so it is Bochner integrable there.  We record the two instances that occur in the
Calderón–Zygmund decomposition of `B(c,R) ∖ B(0,r)`:

* `B(c,R) ∖ B(0,r)` itself, where `‖b‖ ≥ r > 0`;
* the off-centre leftover `B(0,R+‖c‖) ∖ B(c,R)`, where `‖b‖ ≥ R - ‖c‖ > 0`. -/

/-- `kDerivCLM` is Bochner integrable on a ball minus a *centred* ball: every point of the region
is at distance at least `r > 0` from the origin. -/
theorem integrableOn_kDerivCLM_ball_diff_ball (c : Work.LWP.R3) {R r : ℝ} (hr : 0 < r) :
    MeasureTheory.IntegrableOn Work.StabilityFar.Decay.kDerivCLM
      (Metric.ball c R \ Metric.ball (0 : Work.LWP.R3) r) MeasureTheory.volume := by
  classical
  have hmeas : MeasurableSet
      (Metric.ball c R \ Metric.ball (0 : Work.LWP.R3) r : Set Work.LWP.R3) :=
    measurableSet_ball.diff measurableSet_ball
  have hfin : volume
      (Metric.ball c R \ Metric.ball (0 : Work.LWP.R3) r : Set Work.LWP.R3) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.sdiff_subset) measure_ball_lt_top
  have hb2 : ∀ b ∈ (Metric.ball c R \ Metric.ball (0 : Work.LWP.R3) r : Set Work.LWP.R3),
      r ≤ ‖b‖ := by
    intro b hb
    have h : ¬ dist b (0 : Work.LWP.R3) < r := by
      simpa [Set.mem_sdiff, Metric.mem_ball] using hb.2
    simpa using not_lt.mp h
  refine MeasureTheory.IntegrableOn.of_bound hfin ?_ (4 / r ^ 3) ?_
  · apply ContinuousOn.aestronglyMeasurable _ hmeas
    intro b hb
    exact (Work.StabilityFar.Decay.continuousAt_kDerivCLM (by
      have : 0 < ‖b‖ := lt_of_lt_of_le hr (hb2 b hb)
      exact norm_pos_iff.mp this)).continuousWithinAt
  · filter_upwards [ae_restrict_mem hmeas] with b hb
    exact Work.StabilityFar.Decay.norm_kDerivCLM_le b r hr (hb2 b hb)

/-- `kDerivCLM` is Bochner integrable on the off-centre leftover `B(0,ρ) ∖ B(c,R)` when the
centre `c` of the removed ball lies strictly inside it (`‖c‖ < R`): then every point of the
region has `‖b‖ ≥ R - ‖c‖ > 0`. -/
theorem integrableOn_kDerivCLM_ball_diff_offcentre_ball (c : Work.LWP.R3) {R ρ : ℝ}
    (hRc : ‖c‖ < R) :
    MeasureTheory.IntegrableOn Work.StabilityFar.Decay.kDerivCLM
      (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball c R) MeasureTheory.volume := by
  classical
  have hmeas : MeasurableSet
      (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball c R : Set Work.LWP.R3) :=
    measurableSet_ball.diff measurableSet_ball
  have hfin : volume
      (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball c R : Set Work.LWP.R3) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.sdiff_subset) measure_ball_lt_top
  have hm : 0 < R - ‖c‖ := by linarith [norm_nonneg c]
  have hb2 : ∀ b ∈ (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball c R : Set Work.LWP.R3),
      R - ‖c‖ ≤ ‖b‖ := by
    intro b hb
    have h : ¬ dist b c < R := by
      simpa [Set.mem_sdiff, Metric.mem_ball] using hb.2
    have h1 : R ≤ ‖b - c‖ := by
      have := not_lt.mp h
      rwa [dist_eq_norm] at this
    have h2 : ‖b - c‖ ≤ ‖b‖ + ‖c‖ := norm_sub_le b c
    linarith
  refine MeasureTheory.IntegrableOn.of_bound hfin ?_ (4 / (R - ‖c‖) ^ 3) ?_
  · apply ContinuousOn.aestronglyMeasurable _ hmeas
    intro b hb
    exact (Work.StabilityFar.Decay.continuousAt_kDerivCLM (by
      have : 0 < ‖b‖ := lt_of_lt_of_le hm (hb2 b hb)
      exact norm_pos_iff.mp this)).continuousWithinAt
  · filter_upwards [ae_restrict_mem hmeas] with b hb
    exact Work.StabilityFar.Decay.norm_kDerivCLM_le b (R - ‖c‖) hm (hb2 b hb)

/-- **Integrability and a uniform bound for the kernel mass over a ball minus an off-centre ball.**

Let `c : ℝ³`, `R > 0`, `r > 0` with `B(0,r) ⊆ B(c,R)`.  Then `kDerivCLM` is Bochner integrable on
`B(c,R) \ B(0,r)`, and the norm of its integral there is bounded by
`(16π/3) ((R + ‖c‖)^3 / (R - ‖c‖)^3)`, a constant *uniform in `r`*.

The point is the Calderón–Zygmund cancellation: `kDerivCLM` is homogeneous of degree `-3` and has
zero mean over every centred annulus (`integral_kDerivCLM_annulus_eq_zero`), so
`∫_{B(c,R)\B(0,r)} kDerivCLM = - ∫_{B(0,R+‖c‖)\B(c,R)} kDerivCLM` even though `∫‖kDerivCLM‖` over a
region meeting the origin diverges like `log(1/r)`.  The remaining region
`B(0,R+‖c‖) \ B(c,R)` lies in the centred annulus `R-‖c‖ ≤ ‖b‖ ≤ R+‖c‖`, where
`‖kDerivCLM b‖ ≤ 4/(R-‖c‖)^3` and whose volume is at most `(4π/3)(R+‖c‖)^3`. -/
theorem integrableOn_and_norm_setIntegral_kDerivCLM_diff_ball {c : Work.LWP.R3} {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hsub : Metric.ball (0 : Work.LWP.R3) r ⊆ Metric.ball c R) :
    MeasureTheory.IntegrableOn Work.StabilityFar.Decay.kDerivCLM
        (Metric.ball c R \ Metric.ball (0 : Work.LWP.R3) r) MeasureTheory.volume ∧
      ‖∫ b in Metric.ball c R \ Metric.ball (0 : Work.LWP.R3) r,
          Work.StabilityFar.Decay.kDerivCLM b‖
        ≤ (16 * Real.pi / 3) * ((R + ‖c‖) ^ 3 / (R - ‖c‖) ^ 3) := by
  classical
  -- `‖c‖ < R`: the origin lies in `B(0,r) ⊆ B(c,R)`.
  have hσR : ‖c‖ < R := by
    have h0 : (0 : Work.LWP.R3) ∈ Metric.ball (0 : Work.LWP.R3) r := by
      rw [Metric.mem_ball, dist_self]
      exact hr
    have h1 := hsub h0
    rwa [Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg] at h1
  have hpos : 0 < R - ‖c‖ := by linarith [norm_nonneg c]
  refine ⟨integrableOn_kDerivCLM_ball_diff_ball c hr, ?_⟩
  -- The three sets of the decomposition: the region `A` we integrate over, the centred annulus
  -- `B` and the off-centre remainder `D`.
  set A : Set Work.LWP.R3 := Metric.ball c R \ Metric.ball (0 : Work.LWP.R3) r with hA
  set B : Set Work.LWP.R3 :=
    Metric.ball (0 : Work.LWP.R3) (R + ‖c‖) \ Metric.ball (0 : Work.LWP.R3) r with hB
  set D : Set Work.LWP.R3 :=
    Metric.ball (0 : Work.LWP.R3) (R + ‖c‖) \ Metric.ball c R with hD
  have hAmeas : MeasurableSet A := by rw [hA]; exact measurableSet_ball.diff measurableSet_ball
  have hBmeas : MeasurableSet B := by rw [hB]; exact measurableSet_ball.diff measurableSet_ball
  have hDmeas : MeasurableSet D := by rw [hD]; exact measurableSet_ball.diff measurableSet_ball
  -- `B(c,R) ⊆ B(0, R + ‖c‖)`.
  have hbR : Metric.ball c R ⊆ Metric.ball (0 : Work.LWP.R3) (R + ‖c‖) := by
    intro b hb
    rw [Metric.mem_ball] at hb ⊢
    calc dist b 0 = ‖b‖ := dist_zero_right b
      _ = ‖(b - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖b - c‖ + ‖c‖ := norm_add_le _ _
      _ = dist b c + ‖c‖ := by rw [dist_eq_norm]
      _ < R + ‖c‖ := by linarith
  have hbr : Metric.ball (0 : Work.LWP.R3) r ⊆ Metric.ball (0 : Work.LWP.R3) (R + ‖c‖) :=
    hsub.trans hbR
  -- The indicator identity `1_A = 1_B - 1_D`.
  have hid : A.indicator Work.StabilityFar.Decay.kDerivCLM
      = B.indicator Work.StabilityFar.Decay.kDerivCLM
        - D.indicator Work.StabilityFar.Decay.kDerivCLM := by
    rw [hA, hB, hD]
    rw [Set.indicator_sdiff hsub, Set.indicator_sdiff hbr, Set.indicator_sdiff hbR]
    abel
  have hIntB : MeasureTheory.Integrable (B.indicator Work.StabilityFar.Decay.kDerivCLM) volume := by
    rw [hB]
    exact integrable_indicator_kDerivCLM_annulus (ρ := R + ‖c‖) hr
  have hIntD : MeasureTheory.Integrable (D.indicator Work.StabilityFar.Decay.kDerivCLM) volume := by
    rw [hD]
    exact (MeasureTheory.integrable_indicator_iff
      (s := Metric.ball (0 : Work.LWP.R3) (R + ‖c‖) \ Metric.ball c R)
      (f := Work.StabilityFar.Decay.kDerivCLM) (μ := volume)
      (measurableSet_ball.diff measurableSet_ball)).mpr
      (integrableOn_kDerivCLM_ball_diff_offcentre_ball c hσR)
  -- The integral identity: the centred annulus contributes nothing.
  have hIntEq_ind : (∫ b, A.indicator Work.StabilityFar.Decay.kDerivCLM b)
      = (∫ b, B.indicator Work.StabilityFar.Decay.kDerivCLM b)
        - (∫ b, D.indicator Work.StabilityFar.Decay.kDerivCLM b) := by
    rw [hid]
    simp only [Pi.sub_apply]
    rw [MeasureTheory.integral_sub hIntB hIntD]
  have hAind : (∫ b in A, Work.StabilityFar.Decay.kDerivCLM b)
      = ∫ b, A.indicator Work.StabilityFar.Decay.kDerivCLM b :=
    (MeasureTheory.integral_indicator hAmeas).symm
  have hBind : (∫ b in B, Work.StabilityFar.Decay.kDerivCLM b)
      = ∫ b, B.indicator Work.StabilityFar.Decay.kDerivCLM b :=
    (MeasureTheory.integral_indicator hBmeas).symm
  have hDind : (∫ b in D, Work.StabilityFar.Decay.kDerivCLM b)
      = ∫ b, D.indicator Work.StabilityFar.Decay.kDerivCLM b :=
    (MeasureTheory.integral_indicator hDmeas).symm
  have hIntEq : (∫ b in A, Work.StabilityFar.Decay.kDerivCLM b)
      = (∫ b in B, Work.StabilityFar.Decay.kDerivCLM b)
        - (∫ b in D, Work.StabilityFar.Decay.kDerivCLM b) := by
    rw [hAind, hBind, hDind, hIntEq_ind]
  have hBzero : ∫ b in B, Work.StabilityFar.Decay.kDerivCLM b = 0 := by
    rw [hB]
    rcases lt_or_ge r (R + ‖c‖) with hlt | hge
    · exact integral_kDerivCLM_annulus_eq_zero hr hlt
    · rw [Set.sdiff_eq_empty.mpr (Metric.ball_subset_ball hge), MeasureTheory.setIntegral_empty]
  have hkey : ‖∫ b in A, Work.StabilityFar.Decay.kDerivCLM b‖
      = ‖∫ b in D, Work.StabilityFar.Decay.kDerivCLM b‖ := by
    rw [hIntEq, hBzero, zero_sub, norm_neg]
  -- The remaining integral over `B(0,R+‖c‖) ∖ B(c,R)` is bounded by the volume of `B(0,R+‖c‖)`.
  have hDfin : volume D < ⊤ := by
    rw [hD]
    exact lt_of_le_of_lt (MeasureTheory.measure_mono Set.sdiff_subset)
      MeasureTheory.measure_ball_lt_top
  have hpt : ∀ b ∈ D, ‖Work.StabilityFar.Decay.kDerivCLM b‖ ≤ 4 / (R - ‖c‖) ^ 3 := by
    intro b hb
    rw [hD] at hb
    have hb3 : R ≤ ‖b - c‖ := by
      have h2 : ¬ dist b c < R := by
        simpa [Set.mem_sdiff, Metric.mem_ball] using hb.2
      rw [dist_eq_norm] at h2
      exact not_lt.mp h2
    have h4 : ‖b - c‖ ≤ ‖b‖ + ‖c‖ := norm_sub_le b c
    exact Work.StabilityFar.Decay.norm_kDerivCLM_le b (R - ‖c‖) (by linarith) (by linarith)
  have hvol : volume.real (Metric.ball (0 : Work.LWP.R3) (R + ‖c‖))
      = (R + ‖c‖) ^ 3 * (Real.pi * 4 / 3) :=
    volume_real_ball_three (x := 0) (r := R + ‖c‖) (by positivity)
  have hsubD : D ⊆ Metric.ball (0 : Work.LWP.R3) (R + ‖c‖) := by
    rw [hD]; exact Set.sdiff_subset
  have hnorm : ‖∫ b in A, Work.StabilityFar.Decay.kDerivCLM b‖
      ≤ (16 * Real.pi / 3) * ((R + ‖c‖) ^ 3 / (R - ‖c‖) ^ 3) := by
    rw [hkey]
    calc ‖∫ b in D, Work.StabilityFar.Decay.kDerivCLM b‖
        ≤ (4 / (R - ‖c‖) ^ 3) * volume.real D :=
          MeasureTheory.norm_setIntegral_le_of_norm_le_const hDfin hpt
      _ ≤ (4 / (R - ‖c‖) ^ 3) * volume.real (Metric.ball (0 : Work.LWP.R3) (R + ‖c‖)) :=
          mul_le_mul_of_nonneg_left (MeasureTheory.measureReal_mono hsubD)
            (div_nonneg (by norm_num) (pow_nonneg (le_of_lt hpos) 3))
      _ = (16 * Real.pi / 3) * ((R + ‖c‖) ^ 3 / (R - ‖c‖) ^ 3) := by
          rw [hvol, div_eq_mul_inv]
          ring_nf
  simpa [hA] using hnorm

end Work.CoreResiduals.BiotSavart.Bundle
