import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.Spaces.cs_integral
import Submission.Work.Elliptic.lintegral_Ici_ofReal_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted `L²` Hardy inequality behind the elliptic estimate `\bar G`

This module proves `Work.Elliptic.Gbar_hardy_lintegral`, the `L²` Hardy estimate used for the
`\bar G` piece of the singular term (Elgindi, Annals 194(3) 2021, §'The singular term').  The
argument is the classical weighted Hardy / Cauchy--Schwarz bound, carried out in two steps:

* `hardy_op_L2_pointwise`: a weighted Cauchy--Schwarz estimate at a single `z`;
* `hardy_op_L2_tonelli`: the Tonelli computation producing the constant `2/(3β-2)`.

The pointwise step is reproduced here verbatim from `hardy_operator_L2.lean` so that this module
does not depend on a module containing a `sorry`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- **Pointwise (weighted Cauchy–Schwarz) step of the Hardy inequality.**

For `β > 1`, `z > 0` and `f` with `f²` integrable on `(0,∞)`,
`(∫_0^z s^{β-1} f(s) ds)² ≤ (2 z^{β/2}/β) · ∫_0^z s^{(3β-2)/2} f(s)² ds`. -/
theorem hardy_op_L2_pointwise (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    (∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
      ≤ 2 * z ^ (β / 2) / β *
        (∫⁻ s in Set.Ioc 0 z,
          ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
  have hz0 : (0 : ℝ) ≤ z := hz.le
  have hb1 : -1 < (β - 2) / 2 := by linarith
  have hb2 : (0 : ℝ) ≤ (3 * β - 2) / 2 := by linarith
  have hb3 : (0 : ℝ) ≤ (3 * β - 2) / 4 := by linarith
  have hfz : IntegrableOn (fun s : ℝ => f s ^ 2) (Set.Ioc 0 z) :=
    hf.mono_set (fun s hs => hs.1)
  -- Step 1: the interval integral of the norm.
  have h1 : ‖∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s‖
      ≤ ∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖ :=
    intervalIntegral.norm_integral_le_integral_norm hz0
  -- Step 2: rewrite the norm integrand as a product.
  have h2 : ∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖
      = ∫ s in Set.Ioc 0 z,
          s ^ ((β - 2) / 4) * (s ^ ((3 * β - 2) / 4) * |f s|) := by
    rw [intervalIntegral.integral_of_le hz0]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s := hs.1
    have hsum : (β - 2) / 4 + (3 * β - 2) / 4 = β - 1 := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    rw [← mul_assoc, ← Real.rpow_add hs0, hsum]
  -- Step 3: `L²` Cauchy–Schwarz on `(0,z]`.
  have hAESu : AEStronglyMeasurable (fun s : ℝ => s ^ ((β - 2) / 4))
      (volume.restrict (Set.Ioc 0 z)) := by
    refine ContinuousOn.aestronglyMeasurable (fun s hs => ?_) measurableSet_Ioc
    exact (Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt hs.1))).continuousWithinAt
  have hu_mem : MemLp (fun s : ℝ => s ^ ((β - 2) / 4)) 2 (volume.restrict (Set.Ioc 0 z)) := by
    rw [memLp_two_iff_integrable_sq hAESu]
    refine IntegrableOn.congr_fun (f := fun s : ℝ => s ^ ((β - 2) / 2)) ?_ ?_ measurableSet_Ioc
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hz0).mp
        (intervalIntegral.intervalIntegrable_rpow' hb1)
    · intro s hs
      change s ^ ((β - 2) / 2) = (s ^ ((β - 2) / 4)) ^ 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.1.le]
      congr 1
      ring
  have hAESv : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 4) * |f s|)
      (volume.restrict (Set.Ioc 0 z)) := by
    have hs1 : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 4))
        (volume.restrict (Set.Ioc 0 z)) :=
      (Real.continuous_rpow_const hb3).aestronglyMeasurable
    have hs2 : AEStronglyMeasurable (fun s : ℝ => |f s|) (volume.restrict (Set.Ioc 0 z)) := by
      have h0 : AEMeasurable (fun s : ℝ => Real.sqrt (f s ^ 2))
          (volume.restrict (Set.Ioc 0 z)) := hfz.aestronglyMeasurable.aemeasurable.sqrt
      refine h0.aestronglyMeasurable.congr ?_
      exact Filter.Eventually.of_forall (fun s => Real.sqrt_sq_eq_abs (f s))
    exact hs1.mul hs2
  have hv_mem : MemLp (fun s : ℝ => s ^ ((3 * β - 2) / 4) * |f s|) 2
      (volume.restrict (Set.Ioc 0 z)) := by
    rw [memLp_two_iff_integrable_sq hAESv]
    refine IntegrableOn.congr_fun
      (f := fun s : ℝ => s ^ ((3 * β - 2) / 2) * f s ^ 2) ?_ ?_ measurableSet_Ioc
    · refine Integrable.mono' (hfz.const_mul (z ^ ((3 * β - 2) / 2))) ?_ ?_
      · have hs1 : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 2))
            (volume.restrict (Set.Ioc 0 z)) :=
          (Real.continuous_rpow_const hb2).aestronglyMeasurable
        exact hs1.mul hfz.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hs0 : 0 < s := hs.1
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) (sq_nonneg _))]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact Real.rpow_le_rpow hs0.le hs.2 hb2
    · intro s hs
      change s ^ ((3 * β - 2) / 2) * f s ^ 2 = (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
      have hB : (s ^ ((3 * β - 2) / 4)) ^ 2 = s ^ ((3 * β - 2) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs.1.le]
        congr 1
        ring
      rw [mul_pow, sq_abs, hB]
  have hcs := Work.Spaces.cs_integral hu_mem hv_mem
  -- Step 4: the two integrals.
  have hu2 : ∫ s in Set.Ioc 0 z, (s ^ ((β - 2) / 4)) ^ 2 = 2 * z ^ (β / 2) / β := by
    have hB : ∀ s : ℝ, 0 < s → (s ^ ((β - 2) / 4)) ^ 2 = s ^ ((β - 2) / 2) := by
      intro s hs
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      congr 1
      ring
    have hcongr : ∫ s in Set.Ioc 0 z, (s ^ ((β - 2) / 4)) ^ 2
        = ∫ s in (0 : ℝ)..z, s ^ ((β - 2) / 2) := by
      rw [intervalIntegral.integral_of_le hz0]
      exact setIntegral_congr_fun measurableSet_Ioc (fun s hs => hB s hs.1)
    rw [hcongr, integral_rpow (Or.inl hb1)]
    rw [show (β - 2) / 2 + 1 = β / 2 by ring]
    rw [Real.zero_rpow (by positivity : (β / 2) ≠ 0)]
    have hb0 : β ≠ 0 := by linarith
    field_simp
    ring_nf
  have hv2 : ∫ s in Set.Ioc 0 z, (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
      = (∫⁻ s in Set.Ioc 0 z,
          ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
    have hB : ∀ s : ℝ, 0 < s → (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
        = s ^ ((3 * β - 2) / 2) * f s ^ 2 := by
      intro s hs
      have hB' : (s ^ ((3 * β - 2) / 4)) ^ 2 = s ^ ((3 * β - 2) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
        congr 1
        ring
      rw [mul_pow, sq_abs, hB']
    have hcongr : ∫ s in Set.Ioc 0 z, (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
        = ∫ s in Set.Ioc 0 z, s ^ ((3 * β - 2) / 2) * f s ^ 2 :=
      setIntegral_congr_fun measurableSet_Ioc (fun s hs => hB s hs.1)
    rw [hcongr]
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 z)]
        (fun s : ℝ => s ^ ((3 * β - 2) / 2) * f s ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_nonneg (Real.rpow_nonneg hs.1.le _) (sq_nonneg _)
    have hAES : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 2) * f s ^ 2)
        (volume.restrict (Set.Ioc 0 z)) := by
      have hs1 : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 2))
          (volume.restrict (Set.Ioc 0 z)) :=
        (Real.continuous_rpow_const hb2).aestronglyMeasurable
      exact hs1.mul hfz.aestronglyMeasurable
    exact integral_eq_lintegral_of_nonneg_ae hnn hAES
  -- Assemble.
  have hI0 : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖ :=
    intervalIntegral.integral_nonneg hz0 (fun s _ => norm_nonneg _)
  have hsq : (‖∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s‖) ^ 2
      ≤ (∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc (∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
      = ‖∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s‖ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
    _ ≤ (∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖) ^ 2 := hsq
    _ = (∫ s in Set.Ioc 0 z,
          s ^ ((β - 2) / 4) * (s ^ ((3 * β - 2) / 4) * |f s|)) ^ 2 := by rw [h2]
    _ ≤ (∫ s in Set.Ioc 0 z, (s ^ ((β - 2) / 4)) ^ 2)
          * (∫ s in Set.Ioc 0 z, (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2) := hcs
    _ = 2 * z ^ (β / 2) / β *
          (∫⁻ s in Set.Ioc 0 z,
            ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by rw [hu2, hv2]



/-! ## The Tonelli step -/

/-- The iterated integral `∫₀^∞ z^{-3β/2} ∫₀^z s^{(3β-2)/2} f(s)² ds dz` evaluated by Tonelli. -/
theorem hardy_op_L2_tonelli (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)))
      = ENNReal.ofReal (2 / (3 * β - 2) * ∫ z in Set.Ioi (0 : ℝ), f z ^ 2) := by
  have hβ2 : (0:ℝ) < 3 * β - 2 := by linarith
  have ha1 : (1:ℝ) < 3 * β / 2 := by linarith
  have hc1 : (0:ℝ) < 3 * β / 2 - 1 := by linarith
  have hAmeas : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ (-(3 * β / 2)))) := by fun_prop
  have hHae : AEMeasurable (fun s : ℝ => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply AEMeasurable.ennreal_ofReal
    exact ((by fun_prop : Measurable (fun s : ℝ => s ^ ((3 * β - 2) / 2))).aemeasurable).mul
      hf.aestronglyMeasurable.aemeasurable
  have hres : ∀ z, (volume.restrict (Set.Ioi (0:ℝ))).restrict (Set.Ioc 0 z)
      = volume.restrict (Set.Ioc 0 z) := by
    intro z
    rw [Measure.restrict_restrict measurableSet_Ioc]
    congr 1
    exact Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self
  have hA : (∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)))
      = ∫⁻ z in Set.Ioi (0:ℝ), ∫⁻ s in Set.Ioi (0:ℝ),
          ENNReal.ofReal (z ^ (-(3 * β / 2))) *
            (Set.Ioc 0 z).indicator (fun s => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) s := by
    refine lintegral_congr fun z => ?_
    have h1 : ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)
        = ∫⁻ s, (Set.Ioc 0 z).indicator
            (fun s => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) s
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
      rw [lintegral_indicator measurableSet_Ioc, hres]
    rw [h1]
    exact (lintegral_const_mul'' _ (hHae.indicator measurableSet_Ioc)).symm
  rw [hA]
  have hUnc : AEMeasurable (Function.uncurry (fun z s => ENNReal.ofReal (z ^ (-(3 * β / 2))) *
        (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s))
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    have hfst : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-(3 * β / 2)))) :=
      hAmeas.comp measurable_fst
    have hsnd : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ ((3 * β - 2) / 2) * f p.2 ^ 2))
        ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) :=
      hHae.comp_snd
    have hS : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1} := by
      have h1 : MeasurableSet {p : ℝ × ℝ | (0:ℝ) < p.2} := measurableSet_Ioi.preimage measurable_snd
      have h2 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := by
        rw [show {p : ℝ × ℝ | p.2 ≤ p.1} = (fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' Set.Ici (0:ℝ) from by
          ext p; simp [sub_nonneg]]
        exact measurableSet_Ici.preimage (measurable_fst.sub measurable_snd)
      have he : {p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1} = {p | (0:ℝ) < p.2} ∩ {p | p.2 ≤ p.1} := by
        ext p; simp [Set.mem_Ioc]
      rw [he]; exact h1.inter h2
    have h2' : AEMeasurable (fun p : ℝ × ℝ => Set.indicator {q : ℝ × ℝ | q.2 ∈ Set.Ioc 0 q.1}
        (fun q => ENNReal.ofReal (q.2 ^ ((3 * β - 2) / 2) * f q.2 ^ 2)) p)
        ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) :=
      hsnd.indicator hS
    refine (hfst.aemeasurable.mul h2').congr ?_
    filter_upwards with p
    rfl
  rw [lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0:ℝ)))
      (ν := volume.restrict (Set.Ioi (0:ℝ)))
      (f := fun z s => ENNReal.ofReal (z ^ (-(3 * β / 2))) *
        (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s) hUnc]
  have hC : ∀ s, (∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
        (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s)
      = (Set.Ioi (0:ℝ)).indicator (fun s => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2) *
          (∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-(3 * β / 2))))) s := by
    intro s
    by_cases hs : s ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem hs]
      have hs0 : 0 < s := hs
      have hind : ∀ z, (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s
          = (Set.Ici s).indicator (fun _ => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) z := by
        intro z
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases h : s ≤ z
        · rw [if_pos (Set.mem_Ioc.mpr ⟨hs0, h⟩), if_pos (Set.mem_Ici.mpr h)]
        · rw [if_neg (fun hc => h (Set.mem_Ioc.mp hc).2), if_neg (fun hc => h (Set.mem_Ici.mp hc))]
      have hind2 : ∀ z, ENNReal.ofReal (z ^ (-(3 * β / 2))) *
            (Set.Ici s).indicator (fun _ => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) z
          = (Set.Ici s).indicator (fun z => ENNReal.ofReal (z ^ (-(3 * β / 2))) *
                ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) z := by
        intro z
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases h : z ∈ Set.Ici s
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, mul_zero]
      have e1 : (∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
            (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s)
          = ∫⁻ z in Set.Ioi (0:ℝ), (Set.Ici s).indicator (fun z => ENNReal.ofReal (z ^ (-(3 * β / 2))) *
              ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) z := by
        rw [lintegral_congr (fun z => by rw [hind z, hind2 z])]
      rw [e1, ← lintegral_indicator measurableSet_Ioi]
      have hst2 : (∫⁻ z, (Set.Ioi (0:ℝ)).indicator ((Set.Ici s).indicator
              (fun z => ENNReal.ofReal (z ^ (-(3 * β / 2))) * ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) z)
          = ∫⁻ z, (Set.Ici s).indicator
              (fun z => ENNReal.ofReal (z ^ (-(3 * β / 2))) * ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) z := by
        refine lintegral_congr (fun z => ?_)
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases hz : z ∈ Set.Ioi (0:ℝ)
        · rw [if_pos hz]
        · rw [if_neg hz, if_neg (fun hc => hz (hs0.trans_le (Set.mem_Ici.mp hc)))]
      rw [hst2, lintegral_indicator measurableSet_Ici]
      rw [lintegral_mul_const'' _ hAmeas.aemeasurable, mul_comm]
    · rw [Set.indicator_of_notMem hs]
      have hind : ∀ z, (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s = 0 := by
        intro z
        rw [Set.indicator_of_notMem]
        intro hc; exact hs (Set.mem_Ioc.mp hc).1
      rw [lintegral_congr (fun z => by rw [hind z, mul_zero])]
      simp
  have hE : ∀ s ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2) * ENNReal.ofReal (s ^ (1 - 3 * β / 2) / (3 * β / 2 - 1))
        = ENNReal.ofReal (1 / (3 * β / 2 - 1)) * ENNReal.ofReal (f s ^ 2) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hp : (0:ℝ) ≤ s ^ ((3 * β - 2) / 2) * f s ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hs0.le _) (sq_nonneg _)
    rw [← ENNReal.ofReal_mul hp]
    have hkey : s ^ ((3 * β - 2) / 2) * s ^ (1 - 3 * β / 2) = 1 := by
      rw [← Real.rpow_add hs0, show (3 * β - 2) / 2 + (1 - 3 * β / 2) = 0 by ring, Real.rpow_zero]
    have harg : s ^ ((3 * β - 2) / 2) * f s ^ 2 * (s ^ (1 - 3 * β / 2) / (3 * β / 2 - 1))
        = 1 / (3 * β / 2 - 1) * f s ^ 2 := by
      calc s ^ ((3 * β - 2) / 2) * f s ^ 2 * (s ^ (1 - 3 * β / 2) / (3 * β / 2 - 1))
          = (s ^ ((3 * β - 2) / 2) * s ^ (1 - 3 * β / 2)) * (f s ^ 2 / (3 * β / 2 - 1)) := by ring
        _ = 1 * (f s ^ 2 / (3 * β / 2 - 1)) := by rw [hkey]
        _ = 1 / (3 * β / 2 - 1) * f s ^ 2 := by ring
    rw [harg, ENNReal.ofReal_mul (le_of_lt (div_pos one_pos hc1))]
  calc ∫⁻ y in Set.Ioi (0:ℝ), ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (x ^ (-(3 * β / 2))) *
        (Set.Ioc 0 x).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) y
      = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2) *
          (∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-(3 * β / 2)))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
        rw [hC s, Set.indicator_of_mem hs]
    _ = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2) *
          ENNReal.ofReal (s ^ (1 - 3 * β / 2) / (3 * β / 2 - 1)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
        rw [lintegral_Ici_ofReal_rpow ha1 hs]
    _ = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (1 / (3 * β / 2 - 1)) * ENNReal.ofReal (f s ^ 2) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => hE s hs)
    _ = ENNReal.ofReal (1 / (3 * β / 2 - 1)) * ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (f s ^ 2) := by
        rw [lintegral_const_mul'' _ (hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    _ = ENNReal.ofReal (1 / (3 * β / 2 - 1)) * ENNReal.ofReal (∫ s in Set.Ioi (0:ℝ), f s ^ 2) := by
        rw [ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall (fun s => sq_nonneg (f s)))]
    _ = ENNReal.ofReal (1 / (3 * β / 2 - 1) * ∫ s in Set.Ioi (0:ℝ), f s ^ 2) := by
        rw [ENNReal.ofReal_mul (le_of_lt (div_pos one_pos hc1))]
    _ = ENNReal.ofReal (2 / (3 * β - 2) * ∫ s in Set.Ioi (0:ℝ), f s ^ 2) := by
        congr 1
        rw [show 1 / (3 * β / 2 - 1) = 2 / (3 * β - 2) by
          rw [div_eq_div_iff (by linarith) (by linarith)]; ring]

/-! ## The target estimate -/

theorem Gbar_hardy_lintegral (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2)).toReal
      ≤ 4 / (β * (3 * β - 2)) * ∫ z in Set.Ioi (0 : ℝ), f z ^ 2 := by
  have hb0 : (0 : ℝ) < β := by linarith
  have hb2 : (0 : ℝ) < 3 * β - 2 := by linarith
  have hJ : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), f z ^ 2 :=
    integral_nonneg (fun z => sq_nonneg (f z))
  have hpoint : ∀ z, (Set.Ioi (0 : ℝ)).indicator
        (fun z => ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2)) z
      ≤ ENNReal.ofReal (2 / β) * (Set.Ioi (0 : ℝ)).indicator
        (fun z => ENNReal.ofReal (z ^ (-(3 * β / 2))) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) z := by
    intro z
    by_cases hz : z ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      have hzpos : 0 < z := hz
      have hrz : (z ^ (-β)) ^ 2 = z ^ (-(2 * β)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
        congr 1
        ring
      have hc3 : z ^ (-(2 * β)) * z ^ (β / 2) = z ^ (-(3 * β / 2)) := by
        rw [← Real.rpow_add hzpos]
        congr 1
        ring
      have hp := hardy_op_L2_pointwise β hβ f hf hzpos
      have hle : (z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
          ≤ (2 / β) * z ^ (-(3 * β / 2)) *
            (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
        rw [mul_pow, hrz]
        calc z ^ (-(2 * β)) * (∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
            ≤ z ^ (-(2 * β)) * ((2 * z ^ (β / 2) / β) *
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal) :=
              mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hzpos.le _)
          _ = (2 / β) * z ^ (-(3 * β / 2)) *
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
              rw [← hc3]
              ring
      refine (ENNReal.ofReal_le_ofReal hle).trans ?_
      rw [show (2 / β) * z ^ (-(3 * β / 2)) *
            (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal
          = (2 / β) * (z ^ (-(3 * β / 2)) *
              (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal) by ring]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Real.rpow_nonneg hzpos.le _)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le (bot_le)) (bot_le)
    · rw [Set.indicator_of_notMem hz]
      exact bot_le
  have hstep : (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2))
      ≤ ENNReal.ofReal (2 / β) *
        (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono hpoint
  have hT := hardy_op_L2_tonelli β hβ f hf
  have hfin : ENNReal.ofReal (2 / β) *
        (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) ≠ ⊤ := by
    rw [hT]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2)).toReal
      ≤ (ENNReal.ofReal (2 / β) *
          (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
            (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)))).toReal :=
        ENNReal.toReal_mono hfin hstep
    _ = (ENNReal.ofReal (2 / β) *
          ENNReal.ofReal (2 / (3 * β - 2) * ∫ z in Set.Ioi 0, f z ^ 2)).toReal := by rw [hT]
    _ = 4 / (β * (3 * β - 2)) * ∫ z in Set.Ioi (0 : ℝ), f z ^ 2 := by
        have h1 : β ≠ 0 := ne_of_gt hb0
        have h2 : (3 * β - 2) ≠ 0 := ne_of_gt hb2
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
            ENNReal.toReal_ofReal (mul_nonneg (by positivity) hJ)]
        field_simp
        ring

end Work.Elliptic
