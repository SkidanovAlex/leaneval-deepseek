import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Submission.Work.BoseBoxFock.SqrtKinDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKin.norm_rpow_radial`

The two elementary radial integrability facts in `ℝ³` that control the Riesz kernel
`‖x - y‖^{-4}` near and far from the diagonal:

* `integrableOn_norm_rpow_neg_two_ball` : `z ↦ ‖z‖ ^ (-2)` is integrable on the unit ball
  (it is the borderline case `α = d - 1 = 2` of `∫_{‖z‖≤1}‖z‖^{-α}`, which converges because
  `α < d = 3`; this is `MeasureTheory.integrableOn_ball_of_norm_le_rpow`);
* `integrableOn_norm_rpow_neg_four_outer` : `z ↦ ‖z‖ ^ (-4)` is integrable on the *outside*
  `{z | 1 ≤ ‖z‖}` (the decay `r^{-4}` beats the volume growth `r³`; this is the polar-coordinate
  change of variables `MeasureTheory.integrable_fun_norm_addHaar`, which reduces it to the
  one-dimensional integral `∫_0^∞ y^{-2}·1_{y ≥ 1} dy`, evaluated by the substitution `y = x^{-1}`,
  `MeasureTheory.integrableOn_Ioi_comp_rpow_iff'`).

These are the two inputs of `riesz_pair_integrable` (integrability of
`(x,y) ↦ ‖x-y‖^{-4}‖g x - g y‖²` for smooth compactly supported `g`).
-/

noncomputable section

open MeasureTheory

open scoped Real

namespace Work.BoseBoxFock.SqrtKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The borderline local integrability of `‖z‖^{-2}` on the unit ball of `ℝ³`. -/
theorem integrableOn_norm_rpow_neg_two_ball :
    IntegrableOn (fun z : ℝ³ => ‖z‖ ^ (-(2 : ℝ))) (Metric.ball 0 1) := by
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (E := ℝ³) (F := ℝ) (μ := volume)
    (by simp : 1 ≤ Module.finrank ℝ ℝ³) (f := fun z : ℝ³ => ‖z‖ ^ (-(2 : ℝ)))
    (C := 1) (α := 2) (r := 1) (by norm_num) ?_ ?_
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    simp
  · exact (by fun_prop : Measurable fun z : ℝ³ => ‖z‖ ^ (-(2 : ℝ))).aestronglyMeasurable

/-- The far-field integrability of `‖z‖^{-4}` outside the unit ball of `ℝ³`. -/
theorem integrableOn_norm_rpow_neg_four_outer :
    IntegrableOn (fun z : ℝ³ => ‖z‖ ^ (-(4 : ℝ))) {z : ℝ³ | 1 ≤ ‖z‖} := by
  rw [← MeasureTheory.integrable_indicator_iff (s := {z : ℝ³ | 1 ≤ ‖z‖}) (by measurability)]
  have heq : (({z : ℝ³ | 1 ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ (-(4 : ℝ))))
      = fun z : ℝ³ => (Set.Ici (1 : ℝ)).indicator (fun y : ℝ => y ^ (-(4 : ℝ))) ‖z‖ := by
    funext z
    by_cases h : 1 ≤ ‖z‖ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  rw [heq]
  refine (MeasureTheory.integrable_fun_norm_addHaar (μ := volume) (E := ℝ³) (F := ℝ)
    (f := fun y : ℝ => (Set.Ici (1 : ℝ)).indicator (fun y : ℝ => y ^ (-(4 : ℝ))) y)).mpr ?_
  have hc : IntegrableOn (fun x : ℝ => (Set.Iic (1 : ℝ)).indicator (fun _ => (1 : ℝ)) x)
      (Set.Ioi 0) := by
    rw [MeasureTheory.integrableOn_indicator_iff measurableSet_Iic, Set.Iic_inter_Ioi]
    exact MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne (by simp)
  have h2 : IntegrableOn (fun y : ℝ =>
      (Set.Ici (1 : ℝ)).indicator (fun z : ℝ => z ^ (-(2 : ℝ))) y) (Set.Ioi 0) := by
    refine (MeasureTheory.integrableOn_Ioi_comp_rpow_iff'
      (f := fun z : ℝ => (Set.Ici (1 : ℝ)).indicator (fun z : ℝ => z ^ (-(2 : ℝ))) z)
      (p := (-1 : ℝ)) (by norm_num)).mp ?_
    refine (MeasureTheory.integrableOn_congr_fun
      (g := fun x : ℝ => (Set.Iic (1 : ℝ)).indicator (fun _ => (1 : ℝ)) x) ?_
      measurableSet_Ioi).mpr hc
    intro x hx
    have hx0 : 0 < x := hx
    simp only [smul_eq_mul]
    by_cases h : x ≤ 1
    · have h2' : (1 : ℝ) ≤ x ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]; exact (one_le_inv₀ hx0).mpr h
      rw [Set.indicator_of_mem (Set.mem_Ici.mpr h2'), Set.indicator_of_mem (Set.mem_Iic.mpr h)]
      rw [show ((-1 : ℝ) - 1) = -(2 : ℝ) by norm_num, Real.rpow_neg hx0.le,
        Real.rpow_neg_one, Real.inv_rpow hx0.le, Real.rpow_neg hx0.le, inv_inv]
      exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hx0 2))
    · have h2' : ¬ (1 : ℝ) ≤ x ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one, not_le]
        exact inv_lt_one_of_one_lt₀ (not_le.mp h)
      have h'' : x ∉ Set.Iic (1 : ℝ) := by simpa using h
      rw [Set.indicator_of_notMem (Set.mem_Ici.not.mpr h2'), Set.indicator_of_notMem h'']
      ring
  refine (MeasureTheory.integrableOn_congr_fun
    (f := fun y : ℝ => y ^ (Module.finrank ℝ ℝ³ - 1) •
      ((Set.Ici (1 : ℝ)).indicator (fun z : ℝ => z ^ (-(4 : ℝ))) y))
    (g := fun y : ℝ => (Set.Ici (1 : ℝ)).indicator (fun z : ℝ => z ^ (-(2 : ℝ))) y) ?_
    measurableSet_Ioi).mpr h2
  intro y hy
  have hy0 : 0 < y := hy
  simp only [smul_eq_mul]
  rw [show Module.finrank ℝ ℝ³ = 3 from by simp]
  norm_num
  by_cases h : 1 ≤ y
  · rw [Set.indicator_of_mem (Set.mem_Ici.mpr h), Set.indicator_of_mem (Set.mem_Ici.mpr h)]
    have hyne : (y : ℝ) ≠ 0 := hy0.ne'
    field_simp
  · rw [Set.indicator_of_notMem (Set.mem_Ici.not.mpr h),
      Set.indicator_of_notMem (Set.mem_Ici.not.mpr h)]
    ring

end Work.BoseBoxFock.SqrtKin
