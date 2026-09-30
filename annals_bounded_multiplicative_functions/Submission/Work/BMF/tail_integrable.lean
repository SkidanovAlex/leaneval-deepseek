import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory Filter

/-- Integrability of the tail integrand `F t · R²/t²` on `{t | R < |t|}`: `F` is nonnegative,
measurable and bounded, so `F t · R²/t² ≤ K · R²/t²`, and `1/t²` is summable on `|t| > R`. -/
theorem tail_integrable (F : ℝ → ℝ) (hFnn : ∀ t, 0 ≤ F t) (hFmeas : Measurable F)
    (K : ℝ) (hK : ∀ t, F t ≤ K) (R : ℝ) (hR : 0 < R) :
    MeasureTheory.IntegrableOn (fun t : ℝ => F t * (R ^ 2 / t ^ 2)) {t : ℝ | R < |t|} := by
  have hset : {t : ℝ | R < |t|} = Set.Ioi R ∪ Set.Iio (-R) := by
    ext t
    show (R < |t|) ↔ R < t ∨ t < -R
    rw [lt_abs]
    have h : R < -t ↔ t < -R := by
      have := neg_lt_neg_iff (a := -R) (b := t); simpa using this
    rw [h]
  -- Integrability of `t ↦ (t²)⁻¹` on the positive tail.
  have hpos : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Ioi R) := by
    have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hR
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := hR.trans ht
    change t ^ (-2 : ℝ) = (t ^ 2)⁻¹
    rw [Real.rpow_neg (x := t) (y := 2) ht0.le]
    norm_num
  -- Integrability of the same function on the negative tail, by symmetry `t ↦ -t`.
  have hneg : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Iio (-R)) := by
    have himg := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_image
      (f := fun t : ℝ => (t ^ 2)⁻¹) (s := Set.Ioi R) (Homeomorph.neg ℝ).measurableEmbedding
    have himage : (fun x : ℝ => -x) '' Set.Ioi R = Set.Iio (-R) := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩
        exact Set.mem_Iio.mpr (neg_lt_neg (Set.mem_Ioi.mp hy))
      · intro hx
        exact ⟨-x, Set.mem_Ioi.mpr (by simpa using neg_lt_neg (Set.mem_Iio.mp hx)), neg_neg x⟩
    rw [himage] at himg
    refine himg.mpr (hpos.congr_fun (fun t _ => ?_) measurableSet_Ioi)
    simp only [Function.comp_apply]
    rw [neg_sq]
  have hunion : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Ioi R ∪ Set.Iio (-R)) :=
    hpos.union hneg
  have hR2 : IntegrableOn (fun t : ℝ => R ^ 2 * (t ^ 2)⁻¹) (Set.Ioi R ∪ Set.Iio (-R)) :=
    hunion.const_mul (R ^ 2)
  have hg : IntegrableOn (fun t : ℝ => K * (R ^ 2 * (t ^ 2)⁻¹)) (Set.Ioi R ∪ Set.Iio (-R)) :=
    hR2.const_mul K
  have hle : ∀ t : ℝ, ‖F t * (R ^ 2 / t ^ 2)‖ ≤ K * (R ^ 2 * (t ^ 2)⁻¹) := by
    intro t
    have hnonneg : 0 ≤ R ^ 2 * (t ^ 2)⁻¹ :=
      mul_nonneg (sq_nonneg R) (inv_nonneg.mpr (sq_nonneg t))
    rw [div_eq_mul_inv, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hFnn t) hnonneg)]
    exact mul_le_mul_of_nonneg_right (hK t) hnonneg
  have hmeas : Measurable (fun t : ℝ => F t * (R ^ 2 / t ^ 2)) :=
    hFmeas.mul (measurable_const.div (measurable_id.pow_const 2))
  rw [hset, IntegrableOn]
  exact Integrable.mono' hg hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hle)

end Work.BMF
