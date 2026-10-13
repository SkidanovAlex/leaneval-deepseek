import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Aux.bcoef_gamCoef_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

set_option maxHeartbeats 1600000

/-- Measurability of the radial block `∑_{q<7} ((Zop^[q] bcoefRad) z · w z)²`. -/
lemma measurable_radSnorm6 :
    Measurable (fun z : ℝ => ∑ q ∈ Finset.range 7,
      ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
        * Work.Spaces.w z) ^ 2) := by
  refine Finset.measurable_sum _ fun j _ => ?_
  have h3 : Measurable (fun a : ℝ =>
      (Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) a * Work.Spaces.w a) :=
    (Work.FTS.StrongPersist.L3Aux.measurable_Zop_iter j).mul
      Work.FTS.StrongPersist.L3Aux.measurable_w
  have hgoal : (fun a : ℝ =>
        ((Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) a
          * Work.Spaces.w a) ^ 2)
      = fun a : ℝ =>
        ((Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) a * Work.Spaces.w a)
        * ((Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) a * Work.Spaces.w a) := by
    funext a; rw [pow_two]
  rw [hgoal]
  exact h3.mul h3

/-- Nonnegativity of the radial block `∑_{q<7} ((Zop^[q] bcoefRad) z · w z)²`. -/
lemma radSnorm6_nonneg (z : ℝ) : 0 ≤ ∑ q ∈ Finset.range 7,
    ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z) ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

-- The `z`-integral of the radial block `∑_{q<7} ((Zop^[q] bcoefRad) z · w z)²` of the order-`6`
-- separation bound, given the pointwise bound `|(Zop^[j] bcoefRad) z · w z| ≤ K/(1+z)` for
-- `j ≤ 6`.  This is the `range 7` analogue of the proved `L3Aux.radSnorm_int_le`
-- (`range 4`, constant `8K²`): the sum is `≤ 7K²/(1+z)²` pointwise and `∫_Iz 1/(1+z)² ≤ 2`
-- (`Work.Elliptic.WtoH_IntZ`), whence `14K²`.  The measurability lemmas
-- `L3Aux.measurable_Zop_iter`, `L3Aux.measurable_w` are in the imported module.
theorem radSnorm6_int_le {K : ℝ} (hK : 0 ≤ K)
    (hrb : ∀ j ≤ 6, ∀ z ∈ Set.Ici (0 : ℝ),
      |(Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z|
        ≤ K / (1 + z)) :
    MeasureTheory.IntegrableOn
        (fun z => ∑ q ∈ Finset.range 7,
          ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
          ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z) ^ 2)
        ≤ 14 * K ^ 2 := by
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (∑ q ∈ Finset.range 7,
          ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
            * Work.Spaces.w z) ^ 2) ≤ 7 * K ^ 2 * (1 / (1 + z) ^ 2) := by
    intro z hz
    have h1z : (0 : ℝ) < 1 + z := by
      have hz0 : 0 ≤ z := hz
      linarith
    have h1 : ∀ j ∈ Finset.range 7,
        ((Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
            * Work.Spaces.w z) ^ 2 ≤ K ^ 2 * (1 / (1 + z) ^ 2) := by
      intro j hj
      have hj6 : j ≤ 6 := by have := Finset.mem_range.mp hj; omega
      have h := hrb j hj6 z hz
      have h2 : ((Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
            * Work.Spaces.w z) ^ 2 ≤ (K / (1 + z)) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ K / (1 + z))]
        exact h
      refine h2.trans (le_of_eq ?_)
      rw [div_pow, one_div]
      ring
    have hsum := Finset.sum_le_sum h1
    refine hsum.trans ?_
    have hsum' : (∑ _j ∈ Finset.range 7, K ^ 2 * (1 / (1 + z) ^ 2))
        = 7 * K ^ 2 * (1 / (1 + z) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hsum']
  have hdom : MeasureTheory.IntegrableOn (fun z : ℝ => 7 * K ^ 2 * (1 / (1 + z) ^ 2))
      Work.Spaces.Iz := Work.Elliptic.WtoH_IntZ.1.const_mul (7 * K ^ 2)
  have hSint : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∑ q ∈ Finset.range 7,
        ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
          * Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    refine hdom.mono' measurable_radSnorm6.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (radSnorm6_nonneg z)]
    exact hpt z hz
  refine ⟨hSint, ?_⟩
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => radSnorm6_nonneg z) hdom
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
  refine hmono.trans ?_
  rw [MeasureTheory.integral_const_mul]
  have h2 : (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) ≤ 2 := Work.Elliptic.WtoH_IntZ.2
  have h3 : (0 : ℝ) ≤ 7 * K ^ 2 := by positivity
  calc 7 * K ^ 2 * (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) ≤ 7 * K ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = 14 * K ^ 2 := by ring

end Work.FTS.StrongPersist.L6Aux
