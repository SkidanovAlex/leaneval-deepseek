import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Momentum

open MeasureTheory Set

/-!
# The tail integral `∫_{|t| ≥ s} 4/t² = 8/s`

This file computes the (one-dimensional) tail integral of `t ↦ 4/t²` over the
exterior of the ball of radius `s > 0` in `ℝ`, in both the closed and the open
form.  Since the integrand is even, the integral over the whole exterior is twice
the integral over the half-line `(s, ∞)`, which is evaluated with
`integral_Ioi_rpow_of_lt` at exponent `-2`.
-/

/-- `∫_{s}^{∞} 4/t² = 4/s` for `s > 0`. -/
private lemma integral_Ioi_div_sq (a : ℝ) (ha : 0 < a) :
    ∫ t in Set.Ioi a, (4 : ℝ) / t ^ 2 = 4 / a := by
  have hcongr : ∫ t in Set.Ioi a, (4 : ℝ) / t ^ 2
      = ∫ t in Set.Ioi a, 4 * t ^ (-2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := ha.trans ht
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le,
      Real.rpow_natCast, div_eq_mul_inv]
  rw [hcongr, integral_const_mul,
    integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) ha]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  ring

/-- `t ↦ 4/t²` is integrable on `(s, ∞)` for `s > 0`. -/
private lemma integrableOn_Ioi_div_sq (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => 4 / t ^ 2) (Set.Ioi a) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) ha
  have h2 : IntegrableOn (fun t : ℝ => 4 * t ^ (-2 : ℝ)) (Set.Ioi a) :=
    show Integrable _ _ from h1.const_mul 4
  refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := ha.trans ht
  show (4 : ℝ) * t ^ (-2 : ℝ) = 4 / t ^ 2
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le,
    Real.rpow_natCast, div_eq_mul_inv]

/-- `t ↦ 4/t²` is integrable on `(-∞, -s]` for `s > 0`. -/
private lemma integrableOn_Iic_neg_div_sq (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => 4 / t ^ 2) (Set.Iic (-a)) := by
  have hcomp : (fun t : ℝ => 4 / t ^ 2) ∘ (fun x : ℝ => -x)
      = (fun t : ℝ => 4 / t ^ 2) := by
    funext x
    simp only [Function.comp_apply]
    rw [neg_sq]
  have he : (fun x : ℝ => -x) ⁻¹' (Set.Iio (-a)) = Set.Ioi a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have hmap : Measure.map (fun x : ℝ => -x) (volume : Measure ℝ) = volume :=
    Measure.map_neg_eq_self volume
  have hiff : IntegrableOn (fun t : ℝ => 4 / t ^ 2) (Set.Iio (-a)) volume ↔
      IntegrableOn ((fun t : ℝ => 4 / t ^ 2) ∘ (fun x : ℝ => -x))
        (Set.Ioi a) volume := by
    have h := MeasurableEmbedding.integrableOn_map_iff (e := fun x : ℝ => -x)
      (show MeasurableEmbedding (fun x : ℝ => -x) from
        (Homeomorph.neg ℝ).measurableEmbedding)
      (f := fun t : ℝ => 4 / t ^ 2) (μ := volume) (s := Set.Iio (-a))
    rw [hmap, he] at h
    exact h
  have hst : IntegrableOn (fun t : ℝ => 4 / t ^ 2) (Set.Iio (-a)) := by
    rw [hiff, hcomp]
    exact integrableOn_Ioi_div_sq a ha
  exact hst.congr_set_ae (Iio_ae_eq_Iic (a := -a)).symm

/-- `∫_{-∞}^{-s} 4/t² = 4/s` for `s > 0`. -/
private lemma integral_Iic_neg_div_sq (a : ℝ) (ha : 0 < a) :
    ∫ t in Set.Iic (-a), (4 : ℝ) / t ^ 2 = 4 / a := by
  rw [← integral_comp_neg_Ioi a (fun t : ℝ => 4 / t ^ 2)]
  rw [show (∫ x in Set.Ioi a, 4 / (-x) ^ 2) = ∫ x in Set.Ioi a, 4 / x ^ 2 from
     setIntegral_congr_fun measurableSet_Ioi (fun x _ => by rw [neg_sq])]
  exact integral_Ioi_div_sq a ha

/-- The closed exterior `{u | s ≤ |u|}` agrees, up to a null set, with the union of
the two half-lines `(s, ∞)` and `(-∞, -s]`. -/
private lemma ge_abs_ae_eq (a : ℝ) :
    ({u : ℝ | a ≤ |u|} : Set ℝ) =ᵐ[volume] (Set.Ioi a ∪ Set.Iic (-a) : Set ℝ) := by
  have hUsub : (Set.Ioi a ∪ Set.Iic (-a)) ⊆ {u : ℝ | a ≤ |u|} := by
    rintro x (hx | hx)
    · rw [Set.mem_Ioi] at hx
      exact le_trans (le_of_lt hx) (le_abs_self x)
    · rw [Set.mem_Iic] at hx
      exact le_trans (show a ≤ -x by linarith) (neg_le_abs x)
  rw [ae_eq_set]
  refine ⟨measure_mono_null ?_ (measure_singleton a), ?_⟩
  · intro x hx
    rw [Set.mem_singleton_iff]
    have hxS : a ≤ |x| := hx.1
    have hx1 : x ∉ Set.Ioi a := fun h => hx.2 (Or.inl h)
    have hx2 : x ∉ Set.Iic (-a) := fun h => hx.2 (Or.inr h)
    have h1 : x ≤ a := not_lt.mp hx1
    have h2 : -a < x := not_le.mp hx2
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at hxS
      linarith
    · rw [abs_of_neg h] at hxS
      linarith
  · exact measure_mono_null (fun x hx => absurd (hUsub hx.1) hx.2) measure_empty

/-- The open exterior `{u | s < |u|}` agrees, up to a null set, with the union of
the two half-lines `(s, ∞)` and `(-∞, -s]`. -/
private lemma lt_abs_ae_eq (a : ℝ) (ha : 0 < a) :
    ({u : ℝ | a < |u|} : Set ℝ) =ᵐ[volume] (Set.Ioi a ∪ Set.Iic (-a) : Set ℝ) := by
  have hSsub : {u : ℝ | a < |u|} ⊆ (Set.Ioi a ∪ Set.Iic (-a)) := by
    intro x hx
    have hx' : a < |x| := hx
    rcases le_or_gt 0 x with h | h
    · left
      rw [abs_of_nonneg h] at hx'
      exact hx'
    · right
      rw [abs_of_neg h] at hx'
      show x ≤ -a
      linarith
  rw [ae_eq_set]
  refine ⟨measure_mono_null (fun x hx => absurd (hSsub hx.1) hx.2) measure_empty, ?_⟩
  · refine measure_mono_null ?_ (measure_singleton (-a))
    intro x hx
    rw [Set.mem_singleton_iff]
    have hxS : ¬ (a < |x|) := hx.2
    rcases hx.1 with h | h
    · rw [Set.mem_Ioi] at h
      rw [abs_of_pos (show 0 < x by linarith)] at hxS
      exact absurd h hxS
    · rw [Set.mem_Iic] at h
      rw [abs_of_neg (show x < 0 by linarith)] at hxS
      have h' : -x ≤ a := not_lt.mp hxS
      linarith

theorem div_sq_abs_ge (s : ℝ) (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun t : ℝ => 4 / t ^ 2) {u : ℝ | s ≤ |u|} ∧
    (∫ t in {u : ℝ | s ≤ |u|}, 4 / t ^ 2 = 8 / s) ∧
    MeasureTheory.IntegrableOn (fun t : ℝ => 4 / t ^ 2) {u : ℝ | s < |u|} ∧
    (∫ t in {u : ℝ | s < |u|}, 4 / t ^ 2 = 8 / s) := by
  have hIoi := integrableOn_Ioi_div_sq s hs
  have hvIoi := integral_Ioi_div_sq s hs
  have hIic := integrableOn_Iic_neg_div_sq s hs
  have hvIic := integral_Iic_neg_div_sq s hs
  have hdisj : Disjoint (Set.Ioi s) (Set.Iic (-s)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_Ioi] at hx1
    rw [Set.mem_Iic] at hx2
    linarith
  have hU : IntegrableOn (fun t : ℝ => 4 / t ^ 2) (Set.Ioi s ∪ Set.Iic (-s)) :=
    hIoi.union hIic
  have hUv : ∫ t in (Set.Ioi s ∪ Set.Iic (-s)), 4 / t ^ 2 = 8 / s := by
    rw [setIntegral_union hdisj measurableSet_Iic hIoi hIic, hvIoi, hvIic]
    ring
  have hae1 := ge_abs_ae_eq s
  have hae2 := lt_abs_ae_eq s hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hU.congr_set_ae hae1
  · rw [setIntegral_congr_set hae1]
    exact hUv
  · exact hU.congr_set_ae hae2
  · rw [setIntegral_congr_set hae2]
    exact hUv

end Work.BoseKinLoc.Momentum
