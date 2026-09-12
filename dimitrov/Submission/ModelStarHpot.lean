import Mathlib
import Submission.ModelStarLevelSet
import Submission.Commons.Analysis.Complex.integrableOn_log_norm_circleMap_of_analytic_off_finite

/-!
# ModelStarHpot -- the potential identity in the form used by the `(N1)` chain

STATUS: research isolate (NOT imported by `Submission.lean`).

`μ₀ = F_*(dθ/2π)` is the harmonic measure of the model star `M = F '' unitCircle`
(`Submission.ModelStarHarmMeasure`) and `U(x) = ∫ log ‖F(e^{iθ}) - x‖ dθ/2π` is
its logarithmic potential, proved to vanish on `M ∖ {0}` in
`Submission.ModelStarPotential`.  This module converts that statement into the
hypothesis

    `∫⁻ y, ofReal (log (D / ‖x - y‖)) ∂μ₀ = ofReal (log D)`

of the polarization lemma `Commons.MeasureTheory.log_kernel_lintegral_ge_of_potential_eq`,
for every `x ∈ M ∖ {0}` and every `D` bounding the diameter of `M`.
-/

noncomputable section

open scoped Real BigOperators Topology ENNReal
open Filter Set Complex MeasureTheory

namespace Submission.ModelStarHpot

open Submission.ModelStarMap
open Submission.ModelStarDisk (diskPhi diskPhi_zero)
open Submission.ModelStarPotential (circleBad hx hx_apply hx_ne_zero_of_mem_ball
  circleBad_spec analyticAt_diskPhi_of_not_mem_bad continuousOn_hx potential norm_hx_eq)
open Submission.ModelStarExterior (unitCircle modelStarImage mem_circle)
open Submission.ModelStarHarmMeasure (circleMeasure harmMeasure harmMeasure_apply
  meas_circleMap_modelF lintegral_harmMeasure)
open Submission.ModelStarLevelSet (levelSetZ levelSetZ_finite)

variable {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}

/-- `log ‖h_x (e^{iθ})‖`, the "disk" form of the logarithmic kernel. -/
noncomputable def W (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (x : ℂ) (θ : ℝ) : ℝ :=
  Real.log ‖hx z₀ r x (circleMap 0 1 θ)‖

/-- `log ‖F(e^{iθ}) - x‖`, the form in which the potential is stated. -/
noncomputable def w (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (x : ℂ) (θ : ℝ) : ℝ :=
  Real.log ‖modelF z₀ r (circleMap 0 1 θ) - x‖

lemma W_eq_w_neg (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi) (x : ℂ) (θ : ℝ) :
    W z₀ r x θ = w z₀ r x (-θ) := by
  have hu : ‖circleMap 0 1 θ‖ = 1 := by rw [_root_.norm_circleMap_zero]; norm_num
  have hu0 : circleMap 0 1 θ ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  rw [W, w, norm_hx_eq (z₀ := z₀) (r := r) hu0 hu]
  congr 1
  rw [circleMap_zero_inv]
  norm_num


/-- `W` is `2π`-periodic. -/
lemma periodic_W (x : ℂ) : Function.Periodic (W z₀ r x) (2 * Real.pi) := by
  intro θ
  simp only [W]
  rw [periodic_circleMap 0 1 θ]

/-- The disk form of the logarithmic kernel is interval integrable, by the
commons lemma `integrableOn_log_norm_circleMap_of_analytic_off_finite`. -/
lemma intervalIntegrable_W
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    {x : ℂ} (hxM : x ∈ modelStarImage z₀ r) (hx0 : x ≠ 0) :
    IntervalIntegrable (W z₀ r x) MeasureTheory.volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff, uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  refine (integrableOn_Icc_iff_integrableOn_Ioc).mp ?_
  exact Commons.Analysis.Complex.integrableOn_log_norm_circleMap_of_analytic_off_finite
    (hx z₀ r x) (circleBad z₀) (circleBad_spec hunit hr hx0)
    (continuousOn_hx hunit hr x)
    (fun z hz hzB => (analyticAt_diskPhi_of_not_mem_bad hunit hz hzB).sub (by fun_prop))
    (fun z hz => hx_ne_zero_of_mem_ball hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi hxM hz)

/-- The logarithmic kernel in potential form is interval integrable. -/
lemma intervalIntegrable_w
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    {x : ℂ} (hxM : x ∈ modelStarImage z₀ r) (hx0 : x ≠ 0) :
    IntervalIntegrable (w z₀ r x) MeasureTheory.volume 0 (2 * Real.pi) := by
  have hW := intervalIntegrable_W hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi hxM hx0
  have hper := periodic_W (z₀ := z₀) (r := r) x
  -- shift the interval by `2π`: `W` is integrable on `(-2π, 0]` as well
  have hshift : IntervalIntegrable (W z₀ r x) MeasureTheory.volume (-(2 * Real.pi)) 0 := by
    have h1 : IntervalIntegrable (fun θ : ℝ => W z₀ r x (θ + 2 * Real.pi))
        MeasureTheory.volume (-(2 * Real.pi)) 0 := by
      have h2 := IntervalIntegrable.comp_sub_right hW (-(2 * Real.pi))
      rw [show (0 : ℝ) + -(2 * Real.pi) = -(2 * Real.pi) from by ring,
        show (2 * Real.pi) + -(2 * Real.pi) = 0 from by ring] at h2
      simpa only [sub_neg_eq_add] using h2
    exact h1.congr (fun θ _ => hper θ)
  -- reflect
  have h3 : IntervalIntegrable (fun θ : ℝ => W z₀ r x (-θ)) MeasureTheory.volume
      (2 * Real.pi) 0 := by
    have h2 := IntervalIntegrable.comp_sub_left hshift 0
    rw [show (0 : ℝ) - -(2 * Real.pi) = 2 * Real.pi from by ring,
      show (0 : ℝ) - 0 = 0 from by ring] at h2
    simpa only [zero_sub] using h2
  refine (h3.symm).congr (fun θ _ => ?_)
  rw [W_eq_w_neg hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi x (-θ), neg_neg]

/-- The interval integral of the logarithmic kernel in potential form vanishes:
this is the (PROVED) statement that the potential of the harmonic measure is
zero on the model star. -/
lemma intervalIntegral_w_eq_zero
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    {x : ℂ} (hxM : x ∈ modelStarImage z₀ r) (hx0 : x ≠ 0) :
    ∫ θ in (0)..(2 * Real.pi), w z₀ r x θ = 0 := by
  have hp := Submission.ModelStarPotential.potential_eq_zero_of_mem_of_ne_zero hs hz₀e hunit hr
    hsum hmono hφinj hφlo hφhi hxM hx0
  rw [potential, Real.circleAverage_def] at hp
  have hne : ((2 * Real.pi)⁻¹ : ℝ) ≠ 0 := by positivity
  exact (smul_eq_zero.mp hp).resolve_left hne


/-- **The `hpot` hypothesis of the polarisation lemma**: for every point
`x ∈ M ∖ {0}` and every `D` bounding the diameter of `M`, the logarithmic
kernel of the harmonic measure integrates to `log D`. -/
theorem hpot
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    {x : ℂ} (hxM : x ∈ modelStarImage z₀ r) (hx0 : x ≠ 0)
    {D : ℝ} (hD : 0 < D)
    (hDiam : ∀ y ∈ modelStarImage z₀ r, ∀ z ∈ modelStarImage z₀ r, ‖y - z‖ ≤ D) :
    ∫⁻ y, ENNReal.ofReal (Real.log (D / ‖x - y‖)) ∂(harmMeasure z₀ r)
      = ENNReal.ofReal (Real.log D) := by
  have hgmeas : Measurable (fun y : ℂ => ENNReal.ofReal (Real.log (D / ‖x - y‖))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact Real.measurable_log.comp
      (measurable_const.div ((measurable_const.sub measurable_id).norm))
  rw [lintegral_harmMeasure (z₀ := z₀) (r := r) hgmeas]
  have hrw : ∀ θ : ℝ,
      modelF z₀ r (Complex.exp ((θ : ℂ) * Complex.I)) = modelF z₀ r (circleMap 0 1 θ) := by
    intro θ; rw [circleMap_zero, Complex.ofReal_one, one_mul]
  have hstep : ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal
      (Real.log (D / ‖x - modelF z₀ r (Complex.exp ((θ : ℂ) * Complex.I))‖))
      = ENNReal.ofReal (2 * Real.pi * Real.log D) := by
    simp_rw [hrw]
    have hnull : MeasureTheory.volume {θ : ℝ | modelF z₀ r (circleMap 0 1 θ) = x} = 0 :=
      Submission.ModelStarLevelSet.volume_setOf_modelF_circleMap_eq hs hz₀e hunit hr hsum hmono
        hφinj hφlo hφhi x
    have hae : (fun θ : ℝ => Real.log (D / ‖x - modelF z₀ r (circleMap 0 1 θ)‖))
        =ᵐ[MeasureTheory.volume] (fun θ => Real.log D - w z₀ r x θ) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{θ : ℝ | modelF z₀ r (circleMap 0 1 θ) = x}ᶜ, ?_, ?_⟩
      · rw [MeasureTheory.mem_ae_iff]; simpa using hnull
      · intro θ hθ
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hθ
        have hne : ‖x - modelF z₀ r (circleMap 0 1 θ)‖ ≠ 0 := by
          rw [norm_ne_zero_iff, sub_ne_zero]
          exact fun h => hθ h.symm
        simp only [w]
        rw [Real.log_div hD.ne' hne, norm_sub_rev]
    have hw_int : IntervalIntegrable (w z₀ r x) MeasureTheory.volume 0 (2 * Real.pi) :=
      intervalIntegrable_w hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi hxM hx0
    have hwIoc : IntegrableOn (w z₀ r x) (Set.Ioc 0 (2 * Real.pi)) MeasureTheory.volume := by
      rw [← uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), ← intervalIntegrable_iff]
      exact hw_int
    have hconst : IntegrableOn (fun _ : ℝ => Real.log D) (Set.Ioc 0 (2 * Real.pi))
        MeasureTheory.volume := by
      rw [← uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), ← intervalIntegrable_iff]
      exact intervalIntegrable_const
    have hsub : IntegrableOn (fun θ : ℝ => Real.log D - w z₀ r x θ)
        (Set.Ioc 0 (2 * Real.pi)) MeasureTheory.volume := hconst.sub hwIoc
    have hVint : IntegrableOn (fun θ : ℝ => Real.log (D / ‖x - modelF z₀ r (circleMap 0 1 θ)‖))
        (Set.Ioc 0 (2 * Real.pi)) MeasureTheory.volume :=
      hsub.congr (hae.filter_mono ae_restrict_le).symm
    have hVnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))]
        (fun θ : ℝ => Real.log (D / ‖x - modelF z₀ r (circleMap 0 1 θ)‖)) := by
      refine Filter.Eventually.of_forall (fun θ => ?_)
      show (0 : ℝ) ≤ Real.log (D / ‖x - modelF z₀ r (circleMap 0 1 θ)‖)
      rcases eq_or_lt_of_le (norm_nonneg (x - modelF z₀ r (circleMap 0 1 θ))) with h0 | hpos
      · rw [← h0, div_zero, Real.log_zero]
      · refine Real.log_nonneg ?_
        rw [one_le_div hpos]
        exact hDiam x hxM (modelF z₀ r (circleMap 0 1 θ))
          ⟨_, mem_circle.mpr (by rw [_root_.norm_circleMap_zero]; norm_num), rfl⟩
    have hval : ∫ θ, Real.log (D / ‖x - modelF z₀ r (circleMap 0 1 θ)‖)
        ∂(MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))) = 2 * Real.pi * Real.log D := by
      rw [MeasureTheory.integral_congr_ae (hae.filter_mono ae_restrict_le)]
      rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      rw [intervalIntegral.integral_sub intervalIntegrable_const hw_int,
        intervalIntegral_w_eq_zero hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi hxM hx0]
      rw [intervalIntegral.integral_const]
      simp
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hVint hVnn, hval]
  rw [hstep, ← ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)]
  congr 1
  field_simp

end Submission.ModelStarHpot
