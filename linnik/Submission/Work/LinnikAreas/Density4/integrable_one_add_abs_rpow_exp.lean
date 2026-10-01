import Mathlib

namespace Work.LinnikAreas.Density4

open MeasureTheory Set Filter Asymptotics
open scoped Topology

theorem integrable_one_add_abs_rpow_exp (c a : ℝ) (ha : 0 < a) :
    MeasureTheory.Integrable (fun t : ℝ => (1 + |t|) ^ c * Real.exp (-(a * |t|))) := by
  set f : ℝ → ℝ := fun t => (1 + |t|) ^ c * Real.exp (-(a * |t|)) with hf
  have ha2 : (0 : ℝ) < a / 2 := by linarith
  have hcont : ContinuousOn f (Ici (0 : ℝ)) := by
    rw [hf]
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.rpow_const ?_ ?_
      · fun_prop
      · intro x hx
        left
        rw [abs_of_nonneg hx]
        have hx0 : (0 : ℝ) ≤ x := hx
        linarith
    · fun_prop
  have hpoint : ∀ᶠ x : ℝ in atTop, ‖(1 + x) ^ c‖ ≤ 2 ^ (max c 0) * ‖x ^ c‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
    have h1 : (1 + x) ^ c ≤ 2 ^ (max c 0) * x ^ c := by
      rcases lt_or_ge 0 c with hc | hc
      · rw [max_eq_left hc.le]
        calc (1 + x) ^ c ≤ (2 * x) ^ c := Real.rpow_le_rpow (by linarith) (by linarith) hc.le
          _ = 2 ^ c * x ^ c := Real.mul_rpow (by norm_num) hx0.le
      · rw [max_eq_right hc, Real.rpow_zero, one_mul]
        exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) hc
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + x) c),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le c)]
    exact h1
  have h3 : (fun x : ℝ => (1 + x) ^ c * Real.exp (-(a * x))) =O[atTop]
      (fun x : ℝ => x ^ c * Real.exp (-(a * x))) :=
    (IsBigO.of_bound (2 ^ (max c 0)) hpoint).mul
      (isBigO_refl (fun x : ℝ => Real.exp (-(a * x))) atTop)
  have h4 : (fun x : ℝ => x ^ c * Real.exp (-(a * x))) =O[atTop]
      (fun x : ℝ => Real.exp (-(a / 2) * x)) := by
    have hL : (fun x : ℝ => x ^ c) =o[atTop] fun x => Real.exp ((a / 2) * x) :=
      isLittleO_rpow_exp_pos_mul_atTop c ha2
    refine (hL.isBigO.mul (isBigO_refl (fun x : ℝ => Real.exp (-(a * x))) atTop)).congr'
      (EventuallyEq.refl _ _) ?_
    filter_upwards with x
    rw [← Real.exp_add]
    ring_nf
  have hfg : f =ᶠ[atTop] (fun x : ℝ => (1 + x) ^ c * Real.exp (-(a * x))) := by
    rw [hf]
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [abs_of_nonneg hx]
  have hbig : f =O[atTop] (fun x : ℝ => Real.exp (-(a / 2) * x)) :=
    (h3.trans h4).congr' hfg.symm (EventuallyEq.refl _ _)
  have hIoi : IntegrableOn f (Ioi (0 : ℝ)) := integrable_of_isBigO_exp_neg ha2 hcont hbig
  have hIci : IntegrableOn f (Ici (0 : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hIoi
  have hIic : IntegrableOn f (Iic (0 : ℝ)) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (measurableEmbedding_neg) (f := f) (s := Iic (0 : ℝ))
    rw [← h]
    simpa [Function.comp_def, hf, abs_neg, neg_preimage, neg_Iic] using hIci
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

end Work.LinnikAreas.Density4
