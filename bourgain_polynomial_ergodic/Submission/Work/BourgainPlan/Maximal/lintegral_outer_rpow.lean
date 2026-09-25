import Mathlib

/-!
# The outer-region radial `ℝ≥0∞`-integral `∫_{|z| > 2s} s^{b-1} |z|^{-b}`

For `b > 1` and `s > 0`,

  `∫⁻ z in {z : ℝ | 2 s < |z|}, ofReal (s ^ (b - 1) * |z| ^ (-b)) = ofReal (2 ^ (2 - b) / (b - 1))`,

independently of `s`. This is the elementary estimate that makes the "outer" (far-field) part of a
dyadic/rpow weight produce a *constant* rather than a factor growing in `s`; it is the reason the
maximal rpow weight in `s` has uniformly bounded `L¹` mass outside a `2s`-neighbourhood of the origin.

The computation is done by hand, without any polar-coordinate machinery: the domain `{|z| > 2s}` is
the disjoint union `(2s, ∞) ∪ (-∞, -2s)`, negation identifies the two halves, and on `(2s, ∞)` the
remaining integral is the elementary improper integral `∫_{2s}^∞ x^{-b} dx = (2s)^{1-b}/(b-1)`
(`integral_Ioi_rpow_of_lt`).
-/

open MeasureTheory
open scoped ENNReal

namespace Work.BourgainPlan.Maximal

theorem lintegral_outer_rpow (b : ℝ) (hb : 1 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s →
      ∫⁻ z in {z : ℝ | 2 * s < |z|}, ENNReal.ofReal (s ^ (b - 1) * |z| ^ (-b))
        ≤ ENNReal.ofReal C := by
  have hC : 0 ≤ 2 ^ (2 - b) / (b - 1) := by
    apply div_nonneg
    · exact le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)
    · linarith
  refine ⟨2 ^ (2 - b) / (b - 1), hC, fun s hs => ?_⟩
  have hs2 : (0:ℝ) < 2 * s := by linarith
  have hbneg : -b < -1 := by linarith
  have hAeq : {z : ℝ | 2 * s < |z|} = Set.Ioi (2*s) ∪ Set.Iio (-(2*s)) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
    rw [lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  rw [hAeq]
  rw [MeasureTheory.lintegral_union measurableSet_Iio (by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    simp only [Set.mem_Ioi] at hz1
    simp only [Set.mem_Iio] at hz2
    linarith)]
  have hpart1 : ∫⁻ z in Set.Ioi (2*s), ENNReal.ofReal (s ^ (b-1) * |z| ^ (-b))
      = ENNReal.ofReal (s ^ (b-1)) * ∫⁻ z in Set.Ioi (2*s), ENNReal.ofReal (z ^ (-b)) := by
    have hcongr : Set.EqOn (fun z => ENNReal.ofReal (s ^ (b-1) * |z| ^ (-b)))
        (fun z => ENNReal.ofReal (s ^ (b-1)) * ENNReal.ofReal (z ^ (-b))) (Set.Ioi (2*s)) := by
      intro z hz
      have hzpos : 0 < z := by
        simp only [Set.mem_Ioi] at hz; linarith
      change ENNReal.ofReal (s ^ (b-1) * |z| ^ (-b)) =
        ENNReal.ofReal (s ^ (b-1)) * ENNReal.ofReal (z ^ (-b))
      rw [abs_of_pos hzpos, ENNReal.ofReal_mul (Real.rpow_nonneg hs.le (b-1))]
    rw [setLIntegral_congr_fun (μ := volume) measurableSet_Ioi hcongr]
    rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (s^(b-1))) _ ENNReal.ofReal_ne_top]
  have hP : ∫⁻ z in Set.Ioi (2*s), ENNReal.ofReal (z ^ (-b))
      = ENNReal.ofReal ((2*s) ^ (1-b) / (b-1)) := by
    have hInt : IntegrableOn (fun z => z ^ (-b)) (Set.Ioi (2*s)) :=
      integrableOn_Ioi_rpow_of_lt hbneg hs2
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (2*s))] (fun z => z ^ (-b)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      simp only [Set.mem_Ioi] at hz
      exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
    have hthis := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := volume.restrict (Set.Ioi (2*s))) hInt hnn
    rw [← hthis]
    congr 1
    rw [integral_Ioi_rpow_of_lt hbneg hs2]
    rw [show -b + 1 = 1 - b by ring]
    rw [show (1:ℝ) - b = -(b-1) by ring]
    rw [div_neg, neg_div, neg_neg]
  have hpart2 : ∫⁻ z in Set.Iio (-(2*s)), ENNReal.ofReal (s ^ (b-1) * |z| ^ (-b))
      = ENNReal.ofReal (s ^ (b-1)) * ∫⁻ z in Set.Ioi (2*s), ENNReal.ofReal (z ^ (-b)) := by
    have hstep : ∫⁻ z in Set.Iio (-(2*s)), ENNReal.ofReal (s ^ (b-1) * |z| ^ (-b))
        = ∫⁻ z in Set.Ioi (2*s), ENNReal.ofReal (s ^ (b-1) * |z| ^ (-b)) := by
      calc ∫⁻ z in Set.Iio (-(2*s)), ENNReal.ofReal (s ^ (b-1) * |z| ^ (-b))
          = ∫⁻ z, (Set.Iio (-(2*s))).indicator
              (fun w => ENNReal.ofReal (s ^ (b-1) * |w| ^ (-b))) z :=
              (MeasureTheory.lintegral_indicator measurableSet_Iio _).symm
        _ = ∫⁻ z, (Set.Iio (-(2*s))).indicator
              (fun w => ENNReal.ofReal (s ^ (b-1) * |w| ^ (-b))) (-z) :=
              (MeasureTheory.lintegral_neg_eq_self _).symm
        _ = ∫⁻ z, (Set.Ioi (2*s)).indicator
              (fun w => ENNReal.ofReal (s ^ (b-1) * |(-w)| ^ (-b))) z := by
              apply MeasureTheory.lintegral_congr
              intro z
              by_cases hz : z ∈ Set.Ioi (2*s)
              · have h1 : -z ∈ Set.Iio (-(2*s)) := by
                  simp only [Set.mem_Ioi] at hz
                  simp only [Set.mem_Iio]; linarith
                rw [Set.indicator_of_mem h1, Set.indicator_of_mem hz]
              · have h1 : -z ∉ Set.Iio (-(2*s)) := by
                  simp only [Set.mem_Ioi, not_lt] at hz
                  simp only [Set.mem_Iio, not_lt]; linarith
                rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hz]
        _ = ∫⁻ z in Set.Ioi (2*s), ENNReal.ofReal (s ^ (b-1) * |(-z)| ^ (-b)) :=
              MeasureTheory.lintegral_indicator measurableSet_Ioi _
        _ = ∫⁻ z in Set.Ioi (2*s), ENNReal.ofReal (s ^ (b-1) * |z| ^ (-b)) := by
              apply setLIntegral_congr_fun (μ := volume) measurableSet_Ioi
              intro z hz
              change ENNReal.ofReal (s ^ (b-1) * |(-z)| ^ (-b)) =
                ENNReal.ofReal (s ^ (b-1) * |z| ^ (-b))
              rw [abs_neg]
    rw [hstep, hpart1]
  rw [hpart1, hpart2, hP]
  have hR : s^(b-1) * ((2*s)^(1-b)/(b-1)) = 2^(1-b)/(b-1) := by
    have hprod : s^(b-1) * (2*s)^(1-b) = 2^(1-b) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hs.le, ← mul_assoc,
          mul_comm (s^(b-1)) (2^(1-b)), mul_assoc,
          ← Real.rpow_add hs (b-1) (1-b),
          show b - 1 + (1 - b) = 0 by ring, Real.rpow_zero, mul_one]
    rw [← mul_div_assoc, hprod]
  have htwo : (2:ℝ) * 2^(1-b) = 2^(2-b) := by
    nth_rewrite 1 [← Real.rpow_one (2:ℝ)]
    rw [← Real.rpow_add (x := 2) (by norm_num) 1 (1-b)]
    congr 1
    ring
  have hkey : ENNReal.ofReal (s ^ (b-1)) * ENNReal.ofReal ((2*s)^(1-b)/(b-1))
             + ENNReal.ofReal (s ^ (b-1)) * ENNReal.ofReal ((2*s)^(1-b)/(b-1))
      = ENNReal.ofReal (2^(2-b)/(b-1)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le (b-1))]
    rw [← two_mul]
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    rw [hR, ← mul_div_assoc, htwo]
  exact le_of_eq hkey

end Work.BourgainPlan.Maximal
