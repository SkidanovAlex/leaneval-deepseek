import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.EllipticEst.Core.thEtaInvIntegralBounds
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

/-- `x^{1+η} sin(2x)^{-(1+η)} ≤ (π/4)^{1+η}` for `0 < x ≤ π/4`. -/
private lemma pow_mul_sin_inv_le {x : ℝ} (hx0 : 0 < x) (hx : x ≤ Real.pi / 4) :
    x ^ (1 + Work.Spaces.eta) * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta))
      ≤ (Real.pi / 4) ^ (1 + Work.Spaces.eta) := by
  have hpi := Real.pi_pos
  have hη : 0 ≤ 1 + Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have hs : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hx, hpi])
  have hsin : 4 * x / Real.pi ≤ Real.sin (2 * x) := by
    have h := Real.mul_le_sin (by linarith : (0:ℝ) ≤ 2 * x)
      (by linarith [hx, hpi] : 2 * x ≤ Real.pi / 2)
    have he : 2 / Real.pi * (2 * x) = 4 * x / Real.pi := by ring
    rwa [he] at h
  have hle : x ≤ (Real.pi / 4) * Real.sin (2 * x) := by
    have hkey := mul_le_mul_of_nonneg_left hsin (show (0:ℝ) ≤ Real.pi / 4 by positivity)
    have hsimp : Real.pi / 4 * (4 * x / Real.pi) = x := by
      calc Real.pi / 4 * (4 * x / Real.pi)
          = (Real.pi / Real.pi) * ((4:ℝ) / 4) * x := by ring
        _ = 1 * 1 * x := by
            rw [div_self (ne_of_gt hpi), div_self (by norm_num : (4:ℝ) ≠ 0)]
        _ = x := by ring
    rwa [hsimp] at hkey
  have h2 : (Real.sin (2 * x)) ^ (1 + Work.Spaces.eta)
      * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta)) = 1 := by
    rw [← Real.rpow_add hs,
      show (1 + Work.Spaces.eta) + (-(1 + Work.Spaces.eta)) = 0 by ring, Real.rpow_zero]
  have hstep : x ^ (1 + Work.Spaces.eta)
      ≤ ((Real.pi / 4) * Real.sin (2 * x)) ^ (1 + Work.Spaces.eta) :=
    Real.rpow_le_rpow hx0.le hle hη
  rw [Real.mul_rpow (by positivity) (le_of_lt hs)] at hstep
  calc x ^ (1 + Work.Spaces.eta) * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta))
      ≤ ((Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (Real.sin (2 * x)) ^ (1 + Work.Spaces.eta))
        * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg (le_of_lt hs) _)
    _ = (Real.pi / 4) ^ (1 + Work.Spaces.eta)
        * ((Real.sin (2 * x)) ^ (1 + Work.Spaces.eta)
          * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta))) := by ring
    _ = (Real.pi / 4) ^ (1 + Work.Spaces.eta) := by rw [h2, mul_one]

/-- The local angular energy `θ ↦ ∫_{(0,θ)} g` tends to `0` at `0⁺`, for `g` integrable on
`(0, π/2)`. -/
private theorem tendsto_localEnergy {g : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn g (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ : ℝ => ∫ t in Set.Ioo 0 θ, g t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hμlim : Filter.Tendsto
      (fun θ : ℝ => (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) (Set.Ioo 0 θ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    refine Filter.Tendsto.congr' (f₁ := fun θ : ℝ => ENNReal.ofReal θ) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
      have hsub : Set.Ioo (0:ℝ) θ ⊆ Set.Ioo 0 (Real.pi / 2) :=
        fun x hx => ⟨hx.1, lt_trans hx.2 hθ.2⟩
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.mpr hsub,
        Real.volume_Ioo, sub_zero]
    · have hcomp' : Filter.Tendsto (fun θ : ℝ => ENNReal.ofReal θ) (nhds 0) (nhds 0) := by
        simpa [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto (0 : ℝ)
      have hid : Filter.Tendsto (fun θ : ℝ => θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
        Filter.Tendsto.mono_right tendsto_id nhdsWithin_le_nhds
      refine Filter.Tendsto.congr' ?_ (hcomp'.comp hid)
      filter_upwards with θ
      rfl
  have hmain := hg.tendsto_setIntegral_nhds_zero hμlim
  refine Filter.Tendsto.congr' (f₁ := fun θ : ℝ => ∫ t in Set.Ioo 0 θ,
      g t ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) ?_ hmain
  filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
  have hsub : Set.Ioo (0:ℝ) θ ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 hθ.2⟩
  rw [← Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume)
    (s := Set.Ioo (0:ℝ) θ) (t := Set.Ioo 0 (Real.pi / 2)) hsub]

/-- The mirror image: `θ ↦ ∫_{(θ, π/2)} g` tends to `0` at `(π/2)⁻`. -/
private theorem tendsto_localEnergyR {g : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn g (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ : ℝ => ∫ t in Set.Ioo θ (Real.pi / 2), g t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hμlim : Filter.Tendsto
      (fun θ : ℝ => (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))
        (Set.Ioo θ (Real.pi / 2)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine Filter.Tendsto.congr' (f₁ := fun θ : ℝ => ENNReal.ofReal (Real.pi / 2 - θ)) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
      have hsub : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo (0:ℝ) (Real.pi / 2) :=
        fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.mpr hsub,
        Real.volume_Ioo]
    · have hcomp' : Filter.Tendsto (fun θ : ℝ => ENNReal.ofReal θ) (nhds 0) (nhds 0) := by
        simpa [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto (0 : ℝ)
      have hid : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        have h2 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
            (nhds (Real.pi / 2 - Real.pi / 2)) :=
          Filter.Tendsto.sub tendsto_const_nhds
            (Filter.Tendsto.mono_right tendsto_id nhdsWithin_le_nhds)
        simpa using h2
      refine Filter.Tendsto.congr' ?_ (hcomp'.comp hid)
      filter_upwards with θ
      rfl
  have hmain := hg.tendsto_setIntegral_nhds_zero hμlim
  refine Filter.Tendsto.congr' (f₁ := fun θ : ℝ => ∫ t in Set.Ioo θ (Real.pi / 2),
      g t ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) ?_ hmain
  filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
  have hsub : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo (0:ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩
  rw [← Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume)
    (s := Set.Ioo θ (Real.pi / 2)) (t := Set.Ioo 0 (Real.pi / 2)) hsub]

/-- The endpoint rate: `f² sin(2θ)^{-(1+η)} → 0` at both endpoints. -/
theorem EndpointRate {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (Filter.Tendsto (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
    (Filter.Tendsto (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hpi := Real.pi_pos
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hpi4 : (0:ℝ) < Real.pi / 4 := by positivity
  have hAoo : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hA.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hf1 : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) := hf.of_le (by norm_num)
  obtain ⟨K, hKpos, hK⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  obtain ⟨hleft, hright⟩ := hK f hf1 hAoo
  have hEL : Filter.Tendsto
      (fun θ : ℝ => ∫ t in Set.Ioo 0 θ,
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := tendsto_localEnergy hAoo
  have hER : Filter.Tendsto
      (fun θ : ℝ => ∫ t in Set.Ioo θ (Real.pi / 2),
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := tendsto_localEnergyR hAoo
  have hlimL : Filter.Tendsto
      (fun θ : ℝ => (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) *
        ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using hEL.const_mul (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
  have hlimR : Filter.Tendsto
      (fun θ : ℝ => (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) *
        ∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa using hER.const_mul (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
  obtain ⟨cL, hcL_tend, hcL_bd⟩ := hleft
  obtain ⟨cR, hcR_tend, hcR_bd⟩ := hright
  have hcL0 : cL = 0 := tendsto_nhds_unique hcL_tend h0
  have hcR0 : cR = 0 := tendsto_nhds_unique hcR_tend h1
  have hbdL : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      (f θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta) *
        ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    have h := hcL_bd θ hθ
    rwa [hcL0, sub_zero] at h
  have hbdR : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      (f θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
        ∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    have h := hcR_bd θ hθ
    rwa [hcR0, sub_zero] at h
  constructor
  · -- left endpoint
    refine squeeze_zero' ?_ ?_ hlimL
    · filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)
    · filter_upwards [Ioo_mem_nhdsGT hpi4] with θ hθ
      have hθ' : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, hpi]⟩
      have h1' := hbdL θ hθ'
      have hs := sin_two_pos hθ'
      have hspow := Real.rpow_nonneg (le_of_lt hs) (-(1 + Work.Spaces.eta))
      have hE : 0 ≤ (∫ t in Set.Ioo 0 θ,
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht =>
          mul_nonneg (sq_nonneg _)
            (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1,
              le_of_lt (lt_trans ht.2 hθ'.2)⟩))
      have h2' := pow_mul_sin_inv_le hθ.1 (le_of_lt hθ.2)
      calc (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
          ≤ (K * θ ^ (1 + Work.Spaces.eta) *
              (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right h1' hspow
        _ = (K * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * (θ ^ (1 + Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) := by ring
        _ ≤ (K * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * (Real.pi / 4) ^ (1 + Work.Spaces.eta) :=
            mul_le_mul_of_nonneg_left h2' (mul_nonneg hKpos.le hE)
        _ = (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) *
            (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
  · -- right endpoint
    refine squeeze_zero' ?_ ?_ hlimR
    · filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)
    · filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 4 < Real.pi / 2 by linarith)]
        with θ hθ
      have h2pi : Real.pi / 4 < θ := hθ.1
      have hθ' : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨by linarith [hpi, h2pi], hθ.2⟩
      have h1' := hbdR θ hθ'
      have hs := sin_two_pos hθ'
      have hspow := Real.rpow_nonneg (le_of_lt hs) (-(1 + Work.Spaces.eta))
      have hE : 0 ≤ (∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht =>
          mul_nonneg (sq_nonneg _)
            (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt (lt_trans hθ'.1 ht.1),
              le_of_lt ht.2⟩))
      have h2' : (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
          * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
            ≤ (Real.pi / 4) ^ (1 + Work.Spaces.eta) := by
        have hsin : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
          rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
        rw [hsin]
        exact pow_mul_sin_inv_le (by linarith [hθ.2]) (by linarith [h2pi])
      calc (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
          ≤ (K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
              (∫ t in Set.Ioo θ (Real.pi / 2),
                (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right h1' hspow
        _ = (K * (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) := by ring
        _ ≤ (K * (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * (Real.pi / 4) ^ (1 + Work.Spaces.eta) :=
            mul_le_mul_of_nonneg_left h2' (mul_nonneg hKpos.le hE)
        _ = (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) *
            (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring

end Work.EllipticEst.Core.i0Aux
