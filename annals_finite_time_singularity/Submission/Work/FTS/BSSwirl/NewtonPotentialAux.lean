import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.QDefs
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.Bundle.integrableOn_and_norm_setIntegral_kDerivCLM_diff_ball =====
section

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
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.continuousAt_bsDerivCLM_param =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

/-- **Continuity of the parametrised `x`-derivative of the Biot–Savart field.**

For a spacetime vorticity `ω` that is `c`-Hölder in `x` with a constant `C ≥ 0` uniform over the
time window `|t - t₀| < δ`, jointly continuous at `(x₀,t₀)` and continuous in `t` at `t₀` for every
fixed `x`, the map `(x,t) ↦ bsDerivCLM (ω(·,t)) ρ x` is continuous at `(x₀,t₀)`.
-/
theorem continuousAt_bsDerivCLM_param {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {δ c C ρ : ℝ} {x₀ : Work.LWP.R3} {t₀ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ t : ℝ, |t - t₀| < δ →
      ∀ a b : Work.LWP.R3, ‖ω a t - ω b t‖ ≤ C * ‖a - b‖ ^ c)
    (hjoint : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω q.1 q.2) (x₀, t₀))
    (htcont : ∀ a : Work.LWP.R3, ContinuousAt (fun t : ℝ => ω a t) t₀) :
    ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      Work.CoreResiduals.BiotSavart.bsDerivCLM (fun y => ω y q.2) ρ q.1) (x₀, t₀) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  -- The modulus of the inner piece tends to `0` as `Δ → 0⁺`.
  have hlim : ContinuousAt (fun Δ : ℝ => 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c) 0 := by
    have hlin : ContinuousAt (fun Δ : ℝ => 3 * Δ / 2) 0 := by fun_prop
    have hrpow : ContinuousAt (fun t : ℝ => t ^ c) (3 * 0 / 2) := by
      simpa using Real.continuousAt_rpow_const (0 : ℝ) c (Or.inr hc.le)
    have h1 : ContinuousAt (fun Δ : ℝ => (3 * Δ / 2) ^ c) 0 :=
      (ContinuousAt.comp (x := (0 : ℝ)) (f := fun Δ : ℝ => 3 * Δ / 2)
        (g := fun t : ℝ => t ^ c) hrpow hlin)
    exact h1.const_mul _
  obtain ⟨r, hrpos, hr⟩ := Metric.continuousAt_iff.mp hlim (ε / 4) hε4
  set Δ : ℝ := min 1 (r / 2) with hΔdef
  have hΔpos : 0 < Δ := lt_min one_pos (by linarith)
  have hΔle1 : Δ ≤ 1 := min_le_left _ _
  have hΔle2 : Δ ≤ 2 := by linarith
  have hLnn : 0 ≤ 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  have hΔsmall : 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c < ε / 4 := by
    have hdist : dist Δ 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hΔpos]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have h0 : 4 * C * (4 * Real.pi / c) * (3 * 0 / 2) ^ c = 0 := by
      rw [show (3 * 0 / 2 : ℝ) = 0 from by norm_num, Real.zero_rpow hc.ne']
      ring
    have h := hr hdist
    rw [Real.dist_eq, h0, sub_zero, abs_of_nonneg hLnn] at h
    exact h
  -- The outer piece is continuous at `(x₀,t₀)`.
  have hOutCont := continuousAt_bsIntegrand_outer (ω := ω) (ρ := ρ) (Δ := Δ)
    hδ hc hC hhold hjoint htcont hΔpos hΔle2
  obtain ⟨r₂, hr₂pos, hr₂⟩ := Metric.continuousAt_iff.mp hOutCont (ε / 4) hε4
  -- The algebraic shape term is continuous at `(x₀,t₀)`.
  have hShapeCont : ContinuousAt
      (fun q : Work.LWP.R3 × ℝ => (4 * Real.pi / 3) • crossL (ω q.1 q.2)) (x₀, t₀) :=
    (continuous_crossL.continuousAt.comp hjoint).const_smul (4 * Real.pi / 3)
  obtain ⟨r₃, hr₃pos, hr₃⟩ := Metric.continuousAt_iff.mp hShapeCont (ε / 4) hε4
  refine ⟨min (min (Δ / 2) δ) (min r₂ r₃), ?_, fun q hq => ?_⟩
  · exact lt_min (lt_min (by linarith) hδ) (lt_min hr₂pos hr₃pos)
  · have hd1 : dist q.1 x₀ ≤ dist q (x₀, t₀) := by rw [Prod.dist_eq]; exact le_max_left _ _
    have hd2 : dist q.2 t₀ ≤ dist q (x₀, t₀) := by rw [Prod.dist_eq]; exact le_max_right _ _
    have hmin1 : min (min (Δ / 2) δ) (min r₂ r₃) ≤ min (Δ / 2) δ := min_le_left _ _
    have hmin2 : min (min (Δ / 2) δ) (min r₂ r₃) ≤ min r₂ r₃ := min_le_right _ _
    have hxq : ‖q.1 - x₀‖ ≤ Δ / 2 := by
      have h1 : dist q.1 x₀ < Δ / 2 :=
        lt_of_le_of_lt hd1 (lt_of_lt_of_le hq (le_trans hmin1 (min_le_left _ _)))
      rw [dist_eq_norm] at h1
      exact le_of_lt h1
    have hwq : |q.2 - t₀| < δ := by
      have h1 : dist q.2 t₀ < δ :=
        lt_of_le_of_lt hd2 (lt_of_lt_of_le hq (le_trans hmin1 (min_le_right _ _)))
      rwa [Real.dist_eq] at h1
    have hqr₂ : dist q (x₀, t₀) < r₂ := lt_of_lt_of_le hq (le_trans hmin2 (min_le_left _ _))
    have hqr₃ : dist q (x₀, t₀) < r₃ := lt_of_lt_of_le hq (le_trans hmin2 (min_le_right _ _))
    have htcont0 : |t₀ - t₀| < δ := by rw [sub_self, abs_zero]; exact hδ
    have hx0 : ‖x₀ - x₀‖ ≤ Δ / 2 := by rw [sub_self, norm_zero]; positivity
    -- Split the defining integral at the fixed centre `x₀` at both points.
    have hsplit_q : bsDerivCLM (fun y => ω y q.2) ρ q.1
        = (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
              bsIntegrand (fun y => ω y q.2) q.1 a)
          + ((∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
              bsIntegrand (fun y => ω y q.2) q.1 a)
            + (4 * Real.pi / 3) • crossL (ω q.1 q.2)) := by
      show (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand (fun y => ω y q.2) q.1 a)
            + (4 * Real.pi / 3) • crossL (ω q.1 q.2) = _
      rw [integral_split (C := C) hc hC (hhold q.2 hwq) x₀ hΔpos hΔle2 hxq]
      abel
    have hsplit_q0 : bsDerivCLM (fun y => ω y t₀) ρ x₀
        = (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
              bsIntegrand (fun y => ω y t₀) x₀ a)
          + ((∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
              bsIntegrand (fun y => ω y t₀) x₀ a)
            + (4 * Real.pi / 3) • crossL (ω x₀ t₀)) := by
      show (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand (fun y => ω y t₀) x₀ a)
            + (4 * Real.pi / 3) • crossL (ω x₀ t₀) = _
      rw [integral_split (C := C) hc hC (hhold t₀ htcont0) x₀ hΔpos hΔle2 hx0]
      abel
    -- The two inner pieces are small, uniformly in `(x,t)`.
    have hIq_lt : ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y q.2) q.1 a‖ < ε / 4 :=
      lt_of_le_of_lt (norm_setIntegral_le_inner (C := C) (c := c) (ρ := ρ) hc hC
        (hhold q.2 hwq) x₀ hΔpos hxq) hΔsmall
    have hIq0_lt : ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y t₀) x₀ a‖ < ε / 4 :=
      lt_of_le_of_lt (norm_setIntegral_le_inner (C := C) (c := c) (ρ := ρ) (x := x₀) hc hC
        (hhold t₀ htcont0) x₀ hΔpos hx0) hΔsmall
    have hA : ‖(∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y q.2) q.1 a)
        - (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y t₀) x₀ a)‖ ≤ _
        := norm_sub_le _ _
    have hB : ‖(∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y q.2) q.1 a)
        - (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
          bsIntegrand (fun y => ω y t₀) x₀ a)‖ < ε / 4 := by
      have h := hr₂ hqr₂
      rw [dist_eq_norm] at h
      simpa using h
    have hC' : ‖(4 * Real.pi / 3) • crossL (ω q.1 q.2)
        - (4 * Real.pi / 3) • crossL (ω x₀ t₀)‖ < ε / 4 := by
      have h := hr₃ hqr₃
      rw [dist_eq_norm] at h
      simpa using h
    change dist (bsDerivCLM (fun y => ω y q.2) ρ q.1)
        (bsDerivCLM (fun y => ω y t₀) ρ x₀) < ε
    rw [hsplit_q, hsplit_q0]
    have htri : ∀ (a1 a2 b1 b2 c1 c2 : Work.LWP.R3 →L[ℝ] Work.LWP.R3),
        dist (a1 + (b1 + c1)) (a2 + (b2 + c2))
          ≤ ‖a1 - a2‖ + ‖b1 - b2‖ + ‖c1 - c2‖ := by
      intro a1 a2 b1 b2 c1 c2
      rw [dist_eq_norm]
      have h : (a1 + (b1 + c1)) - (a2 + (b2 + c2))
          = (a1 - a2) + (b1 - b2) + (c1 - c2) := by abel
      rw [h]
      calc ‖(a1 - a2) + (b1 - b2) + (c1 - c2)‖
          ≤ ‖(a1 - a2) + (b1 - b2)‖ + ‖c1 - c2‖ := norm_add_le _ _
        _ ≤ (‖a1 - a2‖ + ‖b1 - b2‖) + ‖c1 - c2‖ := by
            gcongr; exact norm_add_le _ _
    refine lt_of_le_of_lt (htri _ _ _ _ _ _) ?_
    linarith [hA, hIq_lt, hIq0_lt, hB, hC']

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.FTS.BSSwirl.NewtonPotentialAux =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

open MeasureTheory Metric Filter Set
open scoped Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSSwirl

noncomputable section

/-! ## Elementary auxiliary facts -/

/-- `(‖z‖³)⁻¹ ‖z‖ ≤ (‖z‖²)⁻¹`.  The borderline case `z = 0` is handled by the convention
`0⁻¹ = 0`. -/
lemma inv_cube_mul_self_le (z : R3) :
    (‖z‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖z‖ ≤ (‖z‖ ^ (2 : ℕ) : ℝ)⁻¹ := by
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · rw [← h]
    norm_num
  · have heq : (‖z‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖z‖ = (‖z‖ ^ (2 : ℕ) : ℝ)⁻¹ := by
      field_simp
    rw [heq]

/-- The identity `(‖z‖³)⁻¹ ‖z‖ = (‖z‖²)⁻¹`. -/
lemma inv_cube_mul_self_eq (z : R3) :
    (‖z‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖z‖ = (‖z‖ ^ (2 : ℕ) : ℝ)⁻¹ := by
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · rw [← h]
    norm_num
  · field_simp

/-- `(a ^ n)⁻¹ = a ^ (-n)` for `a ≥ 0`, in real powers. -/
lemma inv_natPow_eq_rpow_neg' {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : (a ^ n)⁻¹ = a ^ (-(n : ℝ)) := by
  rw [← Real.rpow_natCast a n, ← Real.rpow_neg ha (n : ℝ)]

/-- The kernel `kf z = ‖z‖⁻³ • z` tested against `h` is the first-order Taylor coefficient of
`‖·‖⁻¹` at `z`. -/
lemma inner_kf (z h : R3) :
    inner ℝ (Work.StabilityFar.Decay.kf z) h = (‖z‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ z h := by
  rw [Work.StabilityFar.Decay.kf, inner_smul_left]
  simp [innerSL_apply_apply]

/-- Operator-norm bound for `smulRight`. -/
lemma norm_smulRight_le' (v w : R3) : ‖(innerSL ℝ v).smulRight w‖ ≤ ‖v‖ * ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul, innerSL_apply_apply, Real.norm_eq_abs]
  calc |inner ℝ v x| * ‖w‖ ≤ (‖v‖ * ‖x‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (abs_real_inner_le_norm v x) (norm_nonneg w)
    _ = ‖v‖ * ‖w‖ * ‖x‖ := by ring

/-! ## Integrability of the two kernels -/

/-- The scalar kernel `‖u - ·‖⁻³ ⟪u - ·, h⟫` is integrable against a bounded compactly supported
`ω` (it is dominated by `M ‖h‖ ‖u - ·‖⁻²`, integrable in dimension `3`). -/
lemma integrable_inv_cube_inner_smul' {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) (u h : R3) :
    Integrable (fun y => ((‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (u - y) h) • ω y) volume := by
  have hC : 0 ≤ M * ‖h‖ := mul_nonneg hM (norm_nonneg h)
  have hbd : Integrable (fun y : R3 => (Metric.closedBall (0 : R3) R).indicator
      (fun y => (M * ‖h‖) * ((‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹)) y) volume :=
    Work.StabilityFar.Decay.integrable_indicator_inv_sq u hC
  refine Integrable.mono' hbd ?_ ?_
  · have : Measurable (fun y : R3 => (‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (u - y) h) := by
      measurability
    exact this.aestronglyMeasurable.smul hmeas
  · filter_upwards with y
    by_cases hy : y ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem hy]
      have h1 : |(‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (u - y) h|
          ≤ (‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹ * ‖h‖ := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹)]
        calc (‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * |inner ℝ (u - y) h|
            ≤ (‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * (‖u - y‖ * ‖h‖) :=
              mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
          _ = ((‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖u - y‖) * ‖h‖ := by ring
          _ ≤ (‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹ * ‖h‖ :=
              mul_le_mul_of_nonneg_right (inv_cube_mul_self_le _) (norm_nonneg h)
      calc ‖((‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (u - y) h) • ω y‖
          = |(‖u - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (u - y) h| * ‖ω y‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ((‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹ * ‖h‖) * ‖ω y‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ ((‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹ * ‖h‖) * M :=
            mul_le_mul_of_nonneg_left (hbdd y) (by positivity)
        _ = (M * ‖h‖) * ((‖u - y‖ ^ (2 : ℕ) : ℝ)⁻¹) := by ring
    · have hωy : ω y = 0 := by
        by_contra hh
        exact hy (hsupp y hh)
      rw [Set.indicator_of_notMem hy, hωy]
      simp


/-- The operator-valued kernel of `potDeriv` is integrable: it is dominated by
`M ‖x - ·‖⁻²`, integrable in dimension `3` on the support ball. -/
lemma integrable_potDeriv_kernel' {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) (x : R3) :
    Integrable (fun y => (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ •
      (innerSL ℝ (y - x)).smulRight (ω y)) volume := by
  have hbd : Integrable (fun y : R3 => (Metric.closedBall (0 : R3) R).indicator
      (fun y => M * ((‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹)) y) volume :=
    Work.StabilityFar.Decay.integrable_indicator_inv_sq x hM
  refine Integrable.mono' hbd ?_ ?_
  · first
    | exact ((((continuous_const.sub continuous_id).norm.pow 3).measurable.inv).aestronglyMeasurable).smul
            (Continuous.comp_aestronglyMeasurable₂ (ContinuousLinearMap.smulRightL ℝ Work.FTS.BSSwirl.R3 Work.FTS.BSSwirl.R3).continuous₂
              (((innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable) hmeas)
    | measurability
  · filter_upwards with y
    by_cases hy : y ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem hy]
      have h1 : ‖(innerSL ℝ (y - x)).smulRight (ω y)‖ ≤ ‖y - x‖ * M :=
        (norm_smulRight_le' (y - x) (ω y)).trans
          (mul_le_mul_of_nonneg_left (hbdd y) (norm_nonneg (y - x)))
      calc ‖(‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ • (innerSL ℝ (y - x)).smulRight (ω y)‖
          = (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖(innerSL ℝ (y - x)).smulRight (ω y)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * (‖y - x‖ * M) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = M * ((‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹) := by
            rw [norm_sub_rev y x, ← mul_assoc, inv_cube_mul_self_eq (x - y)]
            ring
    · have hωy : ω y = 0 := by
        by_contra hh
        exact hy (hsupp y hh)
      rw [Set.indicator_of_notMem hy, hωy]
      simp

/-- `‖h‖^{3/2} = o(‖h‖)` at `0`. -/
lemma littleO_norm_rpow_three_halves :
    (fun h : R3 => ‖h‖ ^ ((3 : ℝ) / 2)) =o[𝓝 0] (fun h : R3 => h) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : R3) (lt_min one_pos (pow_pos hε 2))] with h hh
  have hnorm : ‖h‖ < min 1 (ε ^ 2) := by simpa [dist_eq_norm] using hh
  rcases eq_or_ne h 0 with rfl | hne
  · rw [norm_zero]
    simp [Real.zero_rpow (by norm_num : ((3 : ℝ) / 2) ≠ 0)]
  · have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hne
    have h2 : ‖h‖ ≤ ε ^ 2 := le_of_lt (lt_of_lt_of_le hnorm (min_le_right _ _))
    have h3 : Real.sqrt ‖h‖ ≤ ε := by
      rw [← Real.sqrt_sq hε.le]
      exact Real.sqrt_le_sqrt h2
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg h) _)]
    rw [show ‖h‖ ^ ((3 : ℝ) / 2) = ‖h‖ * Real.sqrt ‖h‖ by
      rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hpos, Real.rpow_one]]
    calc ‖h‖ * Real.sqrt ‖h‖ ≤ ‖h‖ * ε := mul_le_mul_of_nonneg_left h3 (norm_nonneg h)
      _ = ε * ‖h‖ := by ring

/-! ## The pointwise residual bounds -/

/-- **Crude bound for the Taylor residual** `K(h,y)`. -/
lemma abs_residual_crude (x h y : R3) :
    |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
        + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h|
      ≤ (‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹ + ‖h‖ * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹ := by
  have hab : |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹|
      ≤ (‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹ := by
    have hadd := abs_add_le ((‖(x + h) - y‖)⁻¹) (-(‖x - y‖)⁻¹)
    rw [← sub_eq_add_neg, abs_neg] at hadd
    simpa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖(x + h) - y‖)⁻¹),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖x - y‖)⁻¹)] using hadd
  have hc : |(‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h|
      ≤ ‖h‖ * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹)]
    calc (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * |inner ℝ (x - y) h|
        ≤ (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * (‖x - y‖ * ‖h‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
      _ = ((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * ‖x - y‖) * ‖h‖ := by ring
      _ ≤ (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹ * ‖h‖ :=
          mul_le_mul_of_nonneg_right (inv_cube_mul_self_le _) (norm_nonneg h)
      _ = ‖h‖ * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹ := by ring
  calc |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
        + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h|
      = |((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹)
          + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h| := rfl
    _ ≤ |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹|
        + |(‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h| := abs_add_le _ _
    _ ≤ ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹) + ‖h‖ * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹ :=
        add_le_add hab hc

/-- **Taylor bound for the residual** in the far regime `2‖h‖ ≤ ‖x - y‖`. -/
lemma abs_residual_far (x h y : R3) (hy : 2 * ‖h‖ ≤ ‖x - y‖) :
    |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
        + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h|
      ≤ 10000 * ‖h‖ ^ ((3 : ℝ) / 2) * ‖x - y‖ ^ (-(5 : ℝ) / 2) := by
  have htay := abs_inv_norm_taylor_residual_le (z := x - y) (h := h) hy
  rw [inner_kf] at htay
  have hz : (x - y) + h = (x + h) - y := by abel
  rwa [hz] at htay

end

end Work.FTS.BSSwirl
end
