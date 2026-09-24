import Mathlib

namespace Work.GM.Affine

open MeasureTheory Set

/-- The tail integrals of `x ↦ C / x ^ 2` over `(c, ∞)` and `(-∞, -c)`, for `c > 0`:
both are (absolutely) integrable there, with value `C / c`. -/
theorem tail_inv_sq_integral (C c : ℝ) (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun x : ℝ => C / x ^ 2) (Set.Ioi c) MeasureTheory.volume ∧
    (∫ x in Set.Ioi c, C / x ^ 2) = C / c ∧
    MeasureTheory.IntegrableOn (fun x : ℝ => C / x ^ 2) (Set.Iio (-c)) MeasureTheory.volume ∧
    (∫ x in Set.Iio (-c), C / x ^ 2) = C / c := by
  -- on `(c, ∞)` the integrand is the constant `C` times the real power `x ^ (-2)`.
  have hpt : ∀ x ∈ Ioi c, C / x ^ 2 = C * x ^ (-2 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hc hx
    have h1 : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hx0) 2]
      norm_num
    rw [h1, div_eq_mul_inv]
  -- integrability and value on `(c, ∞)`, from the real-power integral
  have hpow : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hc
  have hmul : IntegrableOn (fun x : ℝ => C * x ^ (-2 : ℝ)) (Ioi c) := hpow.const_mul C
  have hIoi : IntegrableOn (fun x : ℝ => C / x ^ 2) (Ioi c) :=
    hmul.congr_fun (fun x hx => (hpt x hx).symm) measurableSet_Ioi
  have h3 : ∫ x in Ioi c, x ^ (-2 : ℝ) = c⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    ring
  have hint : ∫ x in Ioi c, C / x ^ 2 = C / c := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, h3, div_eq_mul_inv]
  -- transfer to `(-∞, -c)` along the measure preserving involution `x ↦ -x`
  have hIntIio : IntegrableOn (fun x : ℝ => C / x ^ 2) (Iio (-c)) := by
    have h := (MeasurePreserving.integrableOn_comp_preimage
        (Measure.measurePreserving_neg (volume : Measure ℝ))
        (Homeomorph.neg ℝ).measurableEmbedding
        (f := fun x : ℝ => C / x ^ 2) (s := Ioi c)).mpr hIoi
    simpa only [Function.comp_def, neg_sq, neg_preimage, neg_Ioi] using h
  have hint2 : ∫ x in Iio (-c), C / x ^ 2 = C / c := by
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi c (fun x : ℝ => C / x ^ 2)]
    simp only [neg_sq]
    exact hint
  exact ⟨hIoi, hint, hIntIio, hint2⟩

end Work.GM.Affine
