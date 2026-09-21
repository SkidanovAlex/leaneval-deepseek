import Mathlib

namespace Commons.Geometry.Ulam

open Set
open scoped Topology

/-- The secant slope over `[y,z]` is the weighted average of the slopes over
`[y,c]` and `[c,z]` when `y < c < z`. -/
lemma slope_eq_weighted_of_lt {f : ℝ → ℝ} {y c z : ℝ} (hyc : y < c) (hcz : c < z) :
    slope f y z = ((c - y) / (z - y)) * slope f y c +
      ((z - c) / (z - y)) * slope f c z := by
  rw [slope_def_field, slope_def_field, slope_def_field]
  have h1 : z - y ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hyc hcz))
  have h2 : c - y ≠ 0 := sub_ne_zero.mpr (ne_of_gt hyc)
  have h3 : z - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcz)
  field_simp [h1, h2, h3]
  ring

/-- If `f` is concave on `[a,c]` and on `[c,b]`, continuous on `[a,b]`, differentiable
at the seam from both sides, and the one-sided derivatives are ordered downwards,
then `f` is concave on `[a,b]`. -/
lemma concaveOn_Icc_of_concaveOn_left_right_of_seam
    {f : ℝ → ℝ} {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_left : ConcaveOn ℝ (Set.Icc a c) f)
    (hf_right : ConcaveOn ℝ (Set.Icc c b) f)
    (hf_left_diff : DifferentiableWithinAt ℝ f (Set.Icc a c) c)
    (hf_right_diff : DifferentiableWithinAt ℝ f (Set.Icc c b) c)
    (hseam : derivWithin f (Set.Icc c b) c ≤ derivWithin f (Set.Icc a c) c) :
    ConcaveOn ℝ (Set.Icc a b) f := by
  refine concaveOn_of_slope_anti_adjacent (convex_Icc a b) ?_
  intro x y z hx hz hxy hyz
  have hgoal : (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) := by
    by_cases hyc : y ≤ c
    · by_cases hzc : z ≤ c
      · -- all on the left
        have hx' : x ∈ Set.Icc a c := ⟨hx.1, by linarith [hxy, hyc]⟩
        have hz' : z ∈ Set.Icc a c := ⟨by linarith [hx.1, hxy, hyc], hzc⟩
        have := hf_left.slope_anti_adjacent hx' hz' hxy hyz
        simpa only [slope_def_field] using this
      · -- mixed: x < y ≤ c < z
        have hyc' : y ≤ c := hyc
        have hcz : c < z := lt_of_not_ge hzc
        rcases lt_or_eq_of_le hyc' with hy_lt_c | hy_eq_c
        · -- y < c
         have hy_left : y ∈ Set.Icc a c := ⟨by linarith [hx.1, hxy], hyc'⟩
         have hz_right : z ∈ Set.Icc c b := ⟨hcz.le, hz.2⟩
         have hA : (f c - f y) / (c - y) ≤ (f y - f x) / (y - x) := by
           have := hf_left.slope_anti_adjacent ⟨hx.1, by linarith [hxy, hyc']⟩ ⟨hac.le, le_refl c⟩ hxy hy_lt_c
           simpa only [slope_def_field] using this
         have hB : (f z - f c) / (z - c) ≤ (f c - f y) / (c - y) := by
           have h1 : slope f c z ≤ slope f y c :=
             le_trans
               (hf_right.slope_le_derivWithin ⟨le_refl c, hcb.le⟩ hz_right hcz hf_right_diff)
               (le_trans hseam
                 (hf_left.derivWithin_le_slope hy_left ⟨hac.le, le_refl c⟩ hy_lt_c hf_left_diff))
           simpa only [slope_def_field] using h1
         have hw := slope_eq_weighted_of_lt (f := f) hy_lt_c hcz
         rw [slope_def_field, slope_def_field, slope_def_field] at hw
         rw [hw]
         have hβ : 0 ≤ (z - c) / (z - y) :=
           div_nonneg (sub_nonneg.mpr hcz.le) (sub_nonneg.mpr (lt_trans hy_lt_c hcz).le)
         have hsum : (c - y) / (z - y) + (z - c) / (z - y) = 1 := by
           have h1 : z - y ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hy_lt_c hcz))
           field_simp [h1]; ring
         calc ((c - y) / (z - y)) * ((f c - f y) / (c - y)) + ((z - c) / (z - y)) * ((f z - f c) / (z - c))
             ≤ ((c - y) / (z - y)) * ((f c - f y) / (c - y)) + ((z - c) / (z - y)) * ((f c - f y) / (c - y)) :=
               add_le_add le_rfl (mul_le_mul_of_nonneg_left hB hβ)
           _ = (f c - f y) / (c - y) := by rw [← add_mul, hsum, one_mul]
           _ ≤ (f y - f x) / (y - x) := hA
        · -- y = c
         have hxy' : x < c := by rw [hy_eq_c] at hxy; exact hxy
         rw [hy_eq_c]
         have hz_right : z ∈ Set.Icc c b := ⟨hcz.le, hz.2⟩
         have hx_left : x ∈ Set.Icc a c := ⟨hx.1, le_of_lt hxy'⟩
         have h1 : slope f c z ≤ slope f x c :=
           le_trans
             (hf_right.slope_le_derivWithin ⟨le_refl c, hcb.le⟩ hz_right hcz hf_right_diff)
             (le_trans hseam
               (hf_left.derivWithin_le_slope hx_left ⟨hac.le, le_refl c⟩ hxy' hf_left_diff))
         simpa only [slope_def_field] using h1
    · -- c < y
      have hcy : c < y := lt_of_not_ge hyc
      by_cases hxc : c ≤ x
      · -- all on the right
        have hx' : x ∈ Set.Icc c b := ⟨hxc, by linarith [hxy, hyz, hz.2]⟩
        have hz' : z ∈ Set.Icc c b := ⟨by linarith [hxc, hxy, hyz], hz.2⟩
        have := hf_right.slope_anti_adjacent hx' hz' hxy hyz
        simpa only [slope_def_field] using this
      · -- mixed: x < c < y < z
        have hxc' : x < c := lt_of_not_ge hxc
        have hx_left : x ∈ Set.Icc a c := ⟨hx.1, hxc'.le⟩
        have hc_left : c ∈ Set.Icc a c := ⟨hac.le, le_refl c⟩
        have hc_right : c ∈ Set.Icc c b := ⟨le_refl c, hcb.le⟩
        have hy_right : y ∈ Set.Icc c b := ⟨hcy.le, by linarith [hyz, hz.2]⟩
        have hz_right : z ∈ Set.Icc c b := ⟨by linarith [hcy, hyz], hz.2⟩
        have hright : (f z - f y) / (z - y) ≤ (f y - f c) / (y - c) := by
          have := hf_right.slope_anti_adjacent hc_right hz_right hcy hyz
          simpa only [slope_def_field] using this
        have hA : (f y - f c) / (y - c) ≤ (f c - f x) / (c - x) := by
          have h1 : slope f c y ≤ slope f x c :=
            le_trans
              (hf_right.slope_le_derivWithin hc_right hy_right hcy hf_right_diff)
              (le_trans hseam
                (hf_left.derivWithin_le_slope hx_left hc_left hxc' hf_left_diff))
          simpa only [slope_def_field] using h1
        have hw := slope_eq_weighted_of_lt (f := f) hxc' hcy
        rw [slope_def_field, slope_def_field, slope_def_field] at hw
        rw [hw]
        have hα : 0 ≤ (c - x) / (y - x) :=
          div_nonneg (sub_nonneg.mpr hxc'.le) (sub_nonneg.mpr hxy.le)
        have hsum : (c - x) / (y - x) + (y - c) / (y - x) = 1 := by
          have h1 : y - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxy)
          field_simp [h1]; ring
        have hkey : (f y - f c) / (y - c) ≤
            ((c - x) / (y - x)) * ((f c - f x) / (c - x)) + ((y - c) / (y - x)) * ((f y - f c) / (y - c)) := by
          calc (f y - f c) / (y - c)
              = ((c - x) / (y - x)) * ((f y - f c) / (y - c)) + ((y - c) / (y - x)) * ((f y - f c) / (y - c)) := by
                rw [← add_mul, hsum, one_mul]
            _ ≤ ((c - x) / (y - x)) * ((f c - f x) / (c - x)) + ((y - c) / (y - x)) * ((f y - f c) / (y - c)) :=
                add_le_add (mul_le_mul_of_nonneg_left hA hα) le_rfl
        linarith [hright, hkey]
  simpa only [slope_def_field] using hgoal

end Commons.Geometry.Ulam
