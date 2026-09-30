import Mathlib
import Submission.Work.BMF.integrable_exp_neg_abs_cube
import Submission.Work.BMF.exp_neg_cube_integral_le_two
import Submission.Work.BMF.exp_neg_abs_cube_Ioi_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bound for `∫₀^∞ exp(3y²u - u³) du`

We prove that for every `y ≥ 0`,
`∫ u in Ioi 0, exp (3 * y ^ 2 * u - u ^ 3) ≤ 4 * exp (2 * y ^ 3)`.

The proof has three ingredients.

* Substituting `u = w + y` (translation invariance of Lebesgue measure) turns the
  integral into `exp (2*y^3) * ∫ w in Ioi (-y), exp (-3*y*w^2 - w^3)`.
* On `Ioi (-y)` the exponent `-3yw² - w³` is bounded above by `-|w|³`, because for `w < 0`
  one has `-3yw² - w³ ≤ -|w|³  ⟺  -w ≤ 3y/2`, which follows from `-w < y ≤ 3y/2`.
* Finally `∫ w in Ioi (-y), exp (-|w|³) ≤ 2 * ∫_0^∞ exp (-w³) ≤ 4`.
-/

namespace Work.BMF

open MeasureTheory

/-- For `y ≥ 0` and `w > -y` we have `-3yw² - w³ ≤ -|w|³`. -/
lemma neg_three_mul_sq_sub_cube_le_neg_abs_cube (y w : ℝ) (hy : 0 ≤ y) (hw : -y < w) :
    -3 * y * w ^ 2 - w ^ 3 ≤ -(|w| ^ 3) := by
  rcases le_or_gt 0 w with hw0 | hw0
  · rw [abs_of_nonneg hw0]
    nlinarith [sq_nonneg w, hy, hw0]
  · have h3 : (-w) ^ 3 = -(w ^ 3) := by ring
    rw [abs_of_neg hw0, h3]
    have h2 : 0 ≤ w ^ 2 * (2 * w + 3 * y) := mul_nonneg (sq_nonneg w) (by linarith)
    nlinarith [h2]

theorem exp_cube_integral_le (y : ℝ) (hy : 0 ≤ y) :
    ∫ u in Set.Ioi (0 : ℝ), Real.exp (3 * y ^ 2 * u - u ^ 3) ≤ 4 * Real.exp (2 * y ^ 3) := by
  -- Step 1: substitute `u = w + y` and pull out the constant `exp (2*y^3)`.
  have hshift : ∫ u in Set.Ioi (0 : ℝ), Real.exp (3 * y ^ 2 * u - u ^ 3)
      = Real.exp (2 * y ^ 3) * ∫ w in Set.Ioi (-y), Real.exp (-3 * y * w ^ 2 - w ^ 3) := by
    have hshift' : ∫ u in Set.Ioi (0 : ℝ), Real.exp (3 * y ^ 2 * u - u ^ 3)
        = ∫ w in Set.Ioi (-y), Real.exp (3 * y ^ 2 * (w + y) - (w + y) ^ 3) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
          ← MeasureTheory.integral_indicator measurableSet_Ioi]
      have h1 : (Set.Ioi (0:ℝ)).indicator (fun u => Real.exp (3 * y ^ 2 * u - u ^ 3))
          = fun x => (Set.Ioi (-y)).indicator
              (fun w => Real.exp (3 * y ^ 2 * (w + y) - (w + y) ^ 3)) (x - y) := by
        funext x
        by_cases hx : x ∈ Set.Ioi (0:ℝ)
        · rw [Set.indicator_of_mem hx]
          have hxy : x - y ∈ Set.Ioi (-y) := by simp only [Set.mem_Ioi] at hx ⊢; linarith
          rw [Set.indicator_of_mem hxy]
          congr 1
          ring
        · rw [Set.indicator_of_notMem hx]
          have hxy : x - y ∉ Set.Ioi (-y) := by simp only [Set.mem_Ioi] at hx ⊢; linarith
          rw [Set.indicator_of_notMem hxy]
      rw [h1]
      exact MeasureTheory.integral_sub_right_eq_self _ y
    rw [hshift']
    have hcongr : ∫ w in Set.Ioi (-y), Real.exp (3 * y ^ 2 * (w + y) - (w + y) ^ 3)
        = ∫ w in Set.Ioi (-y), Real.exp (2 * y ^ 3) * Real.exp (-3 * y * w ^ 2 - w ^ 3) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hcongr, MeasureTheory.integral_const_mul]
  -- Step 2: compare the shifted integrand with `exp (-|w|³)`.
  have hcmp : ∫ w in Set.Ioi (-y), Real.exp (-3 * y * w ^ 2 - w ^ 3)
      ≤ ∫ w in Set.Ioi (-y), Real.exp (-(|w| ^ 3)) := by
    have hpt : ∀ w ∈ Set.Ioi (-y),
        Real.exp (-3 * y * w ^ 2 - w ^ 3) ≤ Real.exp (-(|w| ^ 3)) := by
      intro w hw
      simp only [Set.mem_Ioi] at hw
      exact Real.exp_le_exp.mpr (neg_three_mul_sq_sub_cube_le_neg_abs_cube y w hy hw)
    have hint : IntegrableOn (fun w : ℝ => Real.exp (-(|w| ^ 3))) (Set.Ioi (-y)) :=
      integrable_exp_neg_abs_cube.integrableOn.mono_set (Set.subset_univ _)
    have hint2 : IntegrableOn (fun w : ℝ => Real.exp (-3 * y * w ^ 2 - w ^ 3))
        (Set.Ioi (-y)) := by
      refine hint.mono' (by fun_prop) ?_
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall (fun w hw => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact hpt w hw)
    exact MeasureTheory.setIntegral_mono_on hint2 hint measurableSet_Ioi hpt
  -- Step 3: assemble the bounds.
  calc ∫ u in Set.Ioi (0 : ℝ), Real.exp (3 * y ^ 2 * u - u ^ 3)
      = Real.exp (2 * y ^ 3) * ∫ w in Set.Ioi (-y), Real.exp (-3 * y * w ^ 2 - w ^ 3) := hshift
    _ ≤ Real.exp (2 * y ^ 3) * ∫ w in Set.Ioi (-y), Real.exp (-(|w| ^ 3)) :=
        mul_le_mul_of_nonneg_left hcmp (Real.exp_pos _).le
    _ ≤ Real.exp (2 * y ^ 3) * (2 * ∫ w in Set.Ioi (0 : ℝ), Real.exp (-(w ^ 3))) :=
        mul_le_mul_of_nonneg_left (exp_neg_abs_cube_Ioi_le y hy) (Real.exp_pos _).le
    _ ≤ Real.exp (2 * y ^ 3) * (2 * 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        linarith [exp_neg_cube_integral_le_two]
    _ = 4 * Real.exp (2 * y ^ 3) := by ring

end Work.BMF
