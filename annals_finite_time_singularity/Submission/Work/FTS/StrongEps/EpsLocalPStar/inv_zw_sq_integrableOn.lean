import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

/-!
# Integrability of `(1/(z·w(z)))²` on `(0,∞)`

Since `w(z) = (1+z)²/z²`, we have `z·w(z) = (1+z)²/z` for `z > 0`, hence

`(1/(z·w(z)))² = z²/(1+z)⁴ ≤ (1+z)^{-2}`,

and `∫_0^∞ (1+s)^{-2} ds = 1 ≤ 2`.  The two helper lemmas below record the
elementary improper integral of the majorant (integrability and its value `1`)
and the pointwise comparison.
-/

/-- The majorant `(1+s)^{-2}` is integrable on `(0,∞)`. -/
private lemma integrableOn_one_add_rpow_neg_two :
    MeasureTheory.IntegrableOn (fun s : ℝ => (1 + s) ^ (-(2 : ℝ))) (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_add_rpow_Ioi_of_lt (a := -(2 : ℝ)) (c := 0) (m := 1)
    (by norm_num) (by norm_num)
  simpa [add_comm] using h

/-- `∫_0^∞ (1+s)^{-2} ds = 1`, via the antiderivative `s ↦ -(1+s)^{-1}`. -/
private lemma integral_one_add_rpow_neg_two :
    ∫ s in Set.Ioi (0 : ℝ), (1 + s) ^ (-(2 : ℝ)) = 1 := by
  have hg : MeasureTheory.IntegrableOn (fun s : ℝ => (1 + s) ^ (-(2 : ℝ)))
      (Set.Ioi (0 : ℝ)) := integrableOn_one_add_rpow_neg_two
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun s : ℝ => -((1 + s) ^ (-(1 : ℝ)))) ((1 + x) ^ (-(2 : ℝ))) x := by
    intro x hx
    have hpos : (0 : ℝ) < 1 + x := by linarith [Set.mem_Ici.mp hx]
    have hd0 : HasDerivAt (fun s : ℝ => 1 + s) (1 : ℝ) x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have hd1 : HasDerivAt (fun s : ℝ => (1 + s) ^ (-(1 : ℝ)))
        (1 * (-(1 : ℝ)) * (1 + x) ^ (-(1 : ℝ) - 1)) x :=
      hd0.rpow_const (Or.inl (ne_of_gt hpos))
    have hd2 : HasDerivAt (fun s : ℝ => -((1 + s) ^ (-(1 : ℝ))))
        (-(1 * (-(1 : ℝ)) * (1 + x) ^ (-(1 : ℝ) - 1))) x := hd1.neg
    have hexp : -(1 : ℝ) - 1 = -(2 : ℝ) := by norm_num
    refine hd2.congr_deriv ?_
    rw [hexp]
    ring
  have htend : Tendsto (fun s : ℝ => -((1 + s) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => (1 + s) ^ (-(1 : ℝ))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq] using
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
          (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    simpa using h1.neg
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hg htend
  rw [hmain]
  simp

/-- Pointwise comparison: for `z > 0`, `(1/(z·w(z)))² ≤ (1+z)^{-2}`. -/
private lemma div_mul_w_sq_le (z : ℝ) (hz : 0 < z) :
    (1 / (z * Work.Spaces.w z)) ^ 2 ≤ (1 + z) ^ (-(2 : ℝ)) := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hzw : z * Work.Spaces.w z = (1 + z) ^ 2 / z := by
    rw [Work.Spaces.w]
    field_simp
  rw [hzw, one_div_div, Real.rpow_neg (le_of_lt h1z), Real.rpow_two, div_pow,
    inv_eq_one_div]
  have h4 : ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 := by ring
  rw [h4]
  have hsq : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith
  calc z ^ 2 / (1 + z) ^ 4 ≤ (1 + z) ^ 2 / (1 + z) ^ 4 :=
        div_le_div_of_nonneg_right hsq (by positivity)
    _ = 1 / (1 + z) ^ 2 := by
        field_simp

theorem inv_zw_sq_integrableOn :
    MeasureTheory.IntegrableOn (fun z : ℝ => (1 / (z * Work.Spaces.w z)) ^ 2) (Set.Ioi (0:ℝ)) ∧
      0 ≤ ∫ z in Set.Ioi (0:ℝ), (1 / (z * Work.Spaces.w z)) ^ 2 ∧
      (∫ z in Set.Ioi (0:ℝ), (1 / (z * Work.Spaces.w z)) ^ 2) ≤ 2 := by
  have hmeas : Measurable (fun z : ℝ => (1 / (z * Work.Spaces.w z)) ^ 2) := by
    unfold Work.Spaces.w
    fun_prop
  have hmaj : MeasureTheory.IntegrableOn (fun s : ℝ => (1 + s) ^ (-(2 : ℝ))) (Set.Ioi (0 : ℝ)) :=
    integrableOn_one_add_rpow_neg_two
  have hle : ∀ z ∈ Set.Ioi (0 : ℝ), (1 / (z * Work.Spaces.w z)) ^ 2 ≤ (1 + z) ^ (-(2 : ℝ)) :=
    fun z hz => div_mul_w_sq_le z hz
  have hint : MeasureTheory.IntegrableOn (fun z : ℝ => (1 / (z * Work.Spaces.w z)) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.mono' hmaj hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle z hz
  refine ⟨hint, ?_, ?_⟩
  · exact integral_nonneg (fun z => by positivity)
  · have hmono := setIntegral_mono_on hint hmaj measurableSet_Ioi hle
    have hval := integral_one_add_rpow_neg_two
    linarith

end Work.FTS.StrongEps.EpsLocalPStar
