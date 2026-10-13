/-
Copyright: work module for the Elgindi finite-time singularity project.

# The right-tail Tonelli swap for the Hardy weight (`HardyRightTonelliSwap`)

For a measurable `f : ℝ → ℝ≥0∞`,

  `∫_(1,∞) 2 z^{-1/2} (∫_(z,∞) f) dz = ∫_(1,∞) f t · 4 (t^{1/2} - 1) dt`.

Both sides are the integral of the nonnegative integrand `A z · f t` over the triangle
`{(z,t) : 1 < z < t}`, computed with `z` resp. `t` as the outer variable.  The change of
order is Tonelli's theorem (`lintegral_Ioi_Ioi_swap`), and the inner integral in the swapped
order is the elementary `∫_1^t 2 z^{-1/2} dz = 4 (t^{1/2} - 1)`
(`lintegral_Ioo_one_ofReal_rpow_neg_half`).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.Elliptic

/-- **Triangle Tonelli swap.**  For a nonnegative measurable kernel `K` on `ℝ × ℝ`, the
iterated integral over the region `{(z,t) : 1 < z < t}` may be computed with either variable
as the outer one: integrating `t` over `(z,∞)` for `z > 1` and integrating `z` over `(1,t)`
for `t > 1` give the same value. -/
theorem lintegral_Ioi_Ioi_swap (K : ℝ → ℝ → ENNReal)
    (hK : AEMeasurable (Function.uncurry K) (volume.prod volume)) :
    (∫⁻ z in Set.Ioi (1:ℝ), ∫⁻ t in Set.Ioi z, K z t)
      = ∫⁻ t in Set.Ioi (1:ℝ), ∫⁻ z in Set.Ioo (1:ℝ) t, K z t := by
  set T : Set (ℝ × ℝ) := {p : ℝ × ℝ | 1 < p.1 ∧ p.1 < p.2} with hT
  have hTmeas : MeasurableSet T := by
    rw [hT]
    exact MeasurableSet.inter (measurable_fst measurableSet_Ioi)
      (isOpen_lt continuous_fst continuous_snd).measurableSet
  let K' : ℝ → ℝ → ENNReal := fun z t => T.indicator (Function.uncurry K) (z, t)
  have hK'meas : AEMeasurable (Function.uncurry K') (volume.prod volume) := by
    have h1 : Function.uncurry K' = T.indicator (Function.uncurry K) := by
      funext p; obtain ⟨a, b⟩ := p; rfl
    rw [h1]; exact hK.indicator hTmeas
  have hK'1 : ∀ z, 1 < z → ∀ t, (Set.Ioi z).indicator (fun t => K z t) t = K' z t := by
    intro z hz t
    change (Set.Ioi z).indicator (fun t => K z t) t = T.indicator (Function.uncurry K) (z, t)
    rw [hT]
    by_cases h : z < t
    · rw [Set.indicator_of_mem (show t ∈ Set.Ioi z from h),
          Set.indicator_of_mem (show (z, t) ∈ {p : ℝ × ℝ | 1 < p.1 ∧ p.1 < p.2} from ⟨hz, h⟩)]
      rfl
    · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi z from h),
          Set.indicator_of_notMem (show (z, t) ∉ {p : ℝ × ℝ | 1 < p.1 ∧ p.1 < p.2} from
            fun hh => h hh.2)]
  have hK'2 : ∀ t, 1 < t → ∀ z, (Set.Ioo (1:ℝ) t).indicator (fun z => K z t) z = K' z t := by
    intro t ht z
    change (Set.Ioo (1:ℝ) t).indicator (fun z => K z t) z = T.indicator (Function.uncurry K) (z, t)
    rw [hT]
    by_cases h : 1 < z ∧ z < t
    · rw [Set.indicator_of_mem (show z ∈ Set.Ioo (1:ℝ) t from h),
          Set.indicator_of_mem (show (z, t) ∈ {p : ℝ × ℝ | 1 < p.1 ∧ p.1 < p.2} from h)]
      rfl
    · rw [Set.indicator_of_notMem (show z ∉ Set.Ioo (1:ℝ) t from h),
          Set.indicator_of_notMem (show (z, t) ∉ {p : ℝ × ℝ | 1 < p.1 ∧ p.1 < p.2} from h)]
  have ha : (∫⁻ z in Set.Ioi (1:ℝ), ∫⁻ t in Set.Ioi z, K z t) = ∫⁻ z, ∫⁻ t, K' z t := by
    rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ Set.Ioi (1:ℝ)
    · rw [Set.indicator_of_mem hz, ← MeasureTheory.lintegral_indicator measurableSet_Ioi]
      exact lintegral_congr fun t => hK'1 z hz t
    · rw [Set.indicator_of_notMem hz]
      have hzero : (fun t => K' z t) = fun _ => 0 := by
        funext t
        change T.indicator (Function.uncurry K) (z, t) = 0
        rw [Set.indicator_of_notMem (show (z, t) ∉ T from by
          rw [hT]; rintro ⟨h1, _⟩; exact hz (mem_Ioi.mpr h1))]
      rw [hzero, lintegral_zero]
  have hb : (∫⁻ t in Set.Ioi (1:ℝ), ∫⁻ z in Set.Ioo (1:ℝ) t, K z t) = ∫⁻ t, ∫⁻ z, K' z t := by
    rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ Set.Ioi (1:ℝ)
    · rw [Set.indicator_of_mem ht, ← MeasureTheory.lintegral_indicator measurableSet_Ioo]
      exact lintegral_congr fun z => hK'2 t ht z
    · rw [Set.indicator_of_notMem ht]
      have hzero : (fun z => K' z t) = fun _ => 0 := by
        funext z
        change T.indicator (Function.uncurry K) (z, t) = 0
        rw [Set.indicator_of_notMem (show (z, t) ∉ T from by
          rw [hT]; rintro ⟨h1, h2⟩; exact ht (mem_Ioi.mpr (lt_trans h1 h2)))]
      rw [hzero, lintegral_zero]
  rw [ha, hb, MeasureTheory.lintegral_lintegral_swap hK'meas]

/-- The elementary integral of the Hardy weight over the interval `(1,t)`:
`∫_1^t 2 z^{-1/2} dz = 4 (t^{1/2} - 1)` for `t ≥ 1`. -/
theorem lintegral_Ioo_one_ofReal_rpow_neg_half (t : ℝ) (ht : 1 ≤ t) :
    ∫⁻ z in Set.Ioo (1:ℝ) t, ENNReal.ofReal (2 * z ^ (-(1/2:ℝ)))
      = ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1)) := by
  have hcont : ContinuousOn (fun z : ℝ => 2 * z ^ (-(1/2:ℝ))) (Set.Icc 1 t) := by
    apply ContinuousOn.const_mul
    exact continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos hx.1)))
  have hint : IntegrableOn (fun z : ℝ => 2 * z ^ (-(1/2:ℝ))) (Set.Ioo (1:ℝ) t) :=
    (ContinuousOn.integrableOn_Icc (μ := volume) hcont).mono_set Set.Ioo_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo (1:ℝ) t)] (fun z : ℝ => 2 * z ^ (-(1/2:ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt (lt_trans one_pos hz.1)) _)
  have hderiv : ∀ x ∈ Set.uIcc (1:ℝ) t,
      HasDerivAt (fun y : ℝ => 4 * y ^ ((1/2:ℝ))) (2 * x ^ (-(1/2:ℝ))) x := by
    intro x hx
    rw [uIcc_of_le ht] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hx.1)
    have h := (Real.hasDerivAt_rpow_const (x := x) (p := (1/2:ℝ)) (Or.inl hx0)).const_mul 4
    convert h using 1
    rw [show (1/2:ℝ) - 1 = -(1/2) by norm_num]; ring
  have hint2 : IntervalIntegrable (fun z : ℝ => 2 * z ^ (-(1/2:ℝ))) volume 1 t := by
    have hc : ContinuousOn (fun z : ℝ => 2 * z ^ (-(1/2:ℝ))) (Set.uIcc 1 t) := by
      rw [uIcc_of_le ht]; exact hcont
    exact hc.intervalIntegrable
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo (f := fun z : ℝ => 2 * z ^ (-(1/2:ℝ)))
      (x := (1:ℝ)) (y := t)]
  rw [← intervalIntegral.integral_of_le ht]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2]
  rw [Real.one_rpow]; ring

theorem HardyRightTonelliSwap (f : ℝ → ENNReal) (hf : Measurable f) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (1:ℝ)))
        (fun z => ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) *
          MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi z)) f)
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (1:ℝ)))
        (fun t => f t * ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1))) := by
  change (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) *
          ∫⁻ t in Set.Ioi z, f t)
      = ∫⁻ t in Set.Ioi (1:ℝ), f t * ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1))
  have hAmeas : Measurable (fun z : ℝ => ENNReal.ofReal (2 * z ^ (-(1/2:ℝ)))) := by measurability
  have hAne : ∀ z : ℝ, ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) ≠ ⊤ := fun z => ENNReal.ofReal_ne_top
  have hK : AEMeasurable (Function.uncurry
      (fun z t : ℝ => ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * f t)) (volume.prod volume) := by
    have hEq : Function.uncurry (fun z t : ℝ => ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * f t)
        = (fun p : ℝ × ℝ => ENNReal.ofReal (2 * p.1 ^ (-(1/2:ℝ)))) *
          (fun p : ℝ × ℝ => f p.2) := rfl
    rw [hEq]
    exact (hAmeas.aemeasurable.comp_fst (ν := volume)).mul (hf.aemeasurable.comp_snd (μ := volume))
  rw [show (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * ∫⁻ t in Set.Ioi z, f t)
      = ∫⁻ z in Set.Ioi (1:ℝ), ∫⁻ t in Set.Ioi z, ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * f t from by
        refine lintegral_congr fun z => ?_
        exact (MeasureTheory.lintegral_const_mul'
          (ENNReal.ofReal (2 * z ^ (-(1/2:ℝ)))) f (hAne z)).symm]
  rw [lintegral_Ioi_Ioi_swap (fun z t : ℝ => ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * f t) hK]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [MeasureTheory.lintegral_mul_const'' (f t) hAmeas.aemeasurable]
  rw [lintegral_Ioo_one_ofReal_rpow_neg_half t ht.le]
  rw [mul_comm]

end Work.Elliptic
