import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Separation.CompletelyRegular

namespace Commons.Analysis.Integral

open MeasureTheory Real
open scoped Real

/-- The function `x ↦ (1 - x) ^ s` is integrable on `(0, 1)` whenever `-1 < s`.
Obtained from `intervalIntegral.integrableOn_Ioo_rpow_iff` by the reflection
`x ↦ 1 - x` (a measure-preserving change of variables). -/
lemma integrableOn_Ioo_one_sub_rpow (s : ℝ) (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => (1 - x) ^ s) (Set.Ioo (0:ℝ) 1) := by
  have hmp : MeasureTheory.MeasurePreserving (fun y : ℝ => 1 - y) MeasureTheory.volume
      MeasureTheory.volume := by
    have h := (MeasureTheory.measurePreserving_add_left MeasureTheory.volume (1:ℝ)).comp
        (Measure.measurePreserving_neg (MeasureTheory.volume : Measure ℝ))
    convert h using 1
    ext y
    simp [Function.comp, sub_eq_add_neg]
  have hemb : MeasurableEmbedding (fun y : ℝ => 1 - y) :=
    (MeasurableEquiv.subLeft (1:ℝ)).measurableEmbedding
  rw [← (hmp.integrableOn_comp_preimage hemb)]
  have hpre : ((fun y : ℝ => 1 - y) ⁻¹' (Set.Ioo (0:ℝ) 1)) = Set.Ioo (0:ℝ) 1 := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  rw [hpre]
  convert (intervalIntegral.integrableOn_Ioo_rpow_iff (s := s) (t := 1) one_pos).mpr hs using 1
  ext y
  simp [sub_sub_cancel]

/-- The function
`x ↦ (1 - x²)^(-1/8) * √(2/(1 + √(1 - x²))) * √x` is integrable on `(0, 1]`.

Its only singularity is at `x = 1`, where it behaves like `√2 * (1 - x)^(-1/8)`,
and `(1 - x)^(-1/8)` is integrable since `1/8 < 1`; near `x = 0` the factor `√x`
keeps it bounded. -/
theorem integrableOn_l2_rpow_eighth_bound_zero_one :
    MeasureTheory.IntegrableOn (fun x : ℝ =>
        (1 - x ^ 2) ^ (-(1 / 8 : ℝ)) * Real.sqrt (2 / (1 + Real.sqrt (1 - x ^ 2))) * Real.sqrt x)
      (Set.Ioc (0:ℝ) 1) := by
  set f : ℝ → ℝ := fun x =>
    (1 - x ^ 2) ^ (-(1 / 8 : ℝ)) * Real.sqrt (2 / (1 + Real.sqrt (1 - x ^ 2))) * Real.sqrt x
    with hfdef
  have hf_meas : Measurable f := by
    rw [hfdef]; measurability
  have hdom : IntegrableOn (fun x : ℝ => (1 - x) ^ (-(1/8:ℝ))) (Set.Ioo (0:ℝ) 1) :=
    integrableOn_Ioo_one_sub_rpow _ (by norm_num)
  have hg : IntegrableOn (fun x : ℝ => Real.sqrt 2 * (1 - x) ^ (-(1/8:ℝ))) (Set.Ioo (0:ℝ) 1) :=
    Integrable.const_mul hdom (Real.sqrt 2)
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) 1)),
      ‖f x‖ ≤ Real.sqrt 2 * (1 - x) ^ (-(1/8:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Set.mem_Ioo] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hc : (-(1/8:ℝ)) < 0 := by norm_num
    have h1x : 0 < 1 - x := by linarith
    have h1x2 : 0 < 1 - x^2 := by nlinarith [hx0, hx1]
    have hxx : x^2 ≤ x := by nlinarith [hx0, hx1]
    have hAle : (1 - x^2) ^ (-(1/8:ℝ)) ≤ (1 - x) ^ (-(1/8:ℝ)) :=
      (Real.rpow_le_rpow_iff_of_neg h1x2 h1x hc).mpr (by linarith)
    have hden : (0:ℝ) < 1 + Real.sqrt (1 - x^2) := by linarith [Real.sqrt_nonneg (1 - x^2)]
    have hB : Real.sqrt (2 / (1 + Real.sqrt (1 - x^2))) ≤ Real.sqrt 2 := by
      apply Real.sqrt_le_sqrt
      rw [div_le_iff₀ hden]
      linarith [Real.sqrt_nonneg (1 - x^2)]
    have hC : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hx1.le
    have hA0 : 0 ≤ (1 - x^2) ^ (-(1/8:ℝ)) := Real.rpow_nonneg h1x2.le _
    have hAn0 : 0 ≤ (1 - x) ^ (-(1/8:ℝ)) := Real.rpow_nonneg h1x.le _
    have hB0 : 0 ≤ Real.sqrt (2 / (1 + Real.sqrt (1 - x^2))) := Real.sqrt_nonneg _
    have hBs0 : 0 ≤ Real.sqrt (2:ℝ) := Real.sqrt_nonneg _
    have hC0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
    have hfnn : 0 ≤ f x := by
      rw [hfdef]; exact mul_nonneg (mul_nonneg hA0 hB0) hC0
    rw [Real.norm_of_nonneg hfnn, hfdef]
    calc (1 - x ^ 2) ^ (-(1/8:ℝ)) * Real.sqrt (2 / (1 + Real.sqrt (1 - x ^ 2))) * Real.sqrt x
        ≤ (1 - x) ^ (-(1/8:ℝ)) * Real.sqrt (2 / (1 + Real.sqrt (1 - x ^ 2))) * Real.sqrt x := by
          gcongr
      _ ≤ (1 - x) ^ (-(1/8:ℝ)) * Real.sqrt 2 * Real.sqrt x := by
          gcongr
      _ ≤ (1 - x) ^ (-(1/8:ℝ)) * Real.sqrt 2 * 1 := by
          gcongr
      _ = Real.sqrt 2 * (1 - x) ^ (-(1/8:ℝ)) := by ring
  have hIoo : IntegrableOn f (Set.Ioo (0:ℝ) 1) := by
    refine Integrable.mono' hg ?_ hbound
    exact hf_meas.aestronglyMeasurable.restrict
  have hf1 : ‖f 1‖ₑ ≠ ⊤ := by
    rw [hfdef]; simp
  have hIoc : IntegrableOn f (Set.Ioc (0:ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (f := f) (a := 0) (b := 1) hf1).mpr hIoo
  simpa only [hfdef] using hIoc

end Commons.Analysis.Integral