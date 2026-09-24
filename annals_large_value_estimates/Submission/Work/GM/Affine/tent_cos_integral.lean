import Mathlib
import Submission.Work.GM.Affine.tent_defs
import Submission.Commons.Analysis.Fourier.triangle_kernel_fourier_inversion

/-!
# The cosine integral of the tent weight `tent T`

We prove the Fourier (cosine) coefficient computation used in `Work.GM.Affine`:

  `∫ u in (-1/2)..(1/2), tent T u * cos (2 π d u) = T^2 * sinc (π d T)^2`  for `0 < T ≤ 1/2`,

which for `d ≠ 0` is `sin (π d T)^2 / (π d)^2` (and equals `T^2` for `d = 0`).

The tent `tent T u = max 0 (T - |u|)` of `Submission/Work/GM/Affine/tent_defs.lean` is `T`
times the unit triangle `Commons.Analysis.Fourier.tri (u/T)`, whose cosine transform is
`Commons.Analysis.Fourier.integral_tri_cos`.  Since `T ≤ 1/2`, the tent is supported in
`(-1/2, 1/2)`, so the interval integral over `(-1/2, 1/2)` is the integral over `ℝ`.
-/

open MeasureTheory

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The tent of half-width `T > 0` is `T` times the unit triangle `tri (u / T)`. -/
lemma tent_eq_mul_tri {T : ℝ} (hT : 0 < T) (u : ℝ) :
    tent T u = T * Commons.Analysis.Fourier.tri (u / T) := by
  rw [tent, Commons.Analysis.Fourier.tri, abs_div, abs_of_pos hT]
  by_cases h : |u| ≤ T
  · have h1 : 0 ≤ 1 - |u| / T := sub_nonneg.mpr ((div_le_one hT).mpr h)
    have h2 : 0 ≤ T - |u| := sub_nonneg.mpr h
    rw [show max (1 - |u| / T) 0 = 1 - |u| / T from max_eq_left h1,
      show max 0 (T - |u|) = T - |u| from max_eq_right h2]
    field_simp
  · rw [not_le] at h
    have h1 : 1 - |u| / T ≤ 0 := sub_nonpos.mpr ((one_le_div hT).mpr h.le)
    have h2 : T - |u| ≤ 0 := sub_nonpos.mpr h.le
    rw [show max (1 - |u| / T) 0 = 0 from max_eq_right h1,
      show max 0 (T - |u|) = 0 from max_eq_left h2]
    ring

/-- The cosine transform of the tent: for `T > 0` and `d : ℤ`,

  `∫ u, tent T u * cos (2 π d u) = T ^ 2 * sinc (π d T) ^ 2`. -/
lemma integral_tent_cos {T : ℝ} (hT : 0 < T) (d : ℤ) :
    ∫ u : ℝ, tent T u * Real.cos (2 * Real.pi * (d : ℝ) * u)
      = T ^ 2 * (Real.sinc (Real.pi * (d : ℝ) * T)) ^ 2 := by
  set g : ℝ → ℝ :=
    fun v => Commons.Analysis.Fourier.tri v * Real.cos (2 * Real.pi * (T * (d : ℝ)) * v)
    with hg
  have hpt : ∀ u : ℝ, tent T u * Real.cos (2 * Real.pi * (d : ℝ) * u) = T * g (u / T) := by
    intro u
    rw [tent_eq_mul_tri hT, hg]
    simp only
    rw [show 2 * Real.pi * (T * (d : ℝ)) * (u / T) = 2 * Real.pi * (d : ℝ) * u by field_simp]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul]
  rw [MeasureTheory.Measure.integral_comp_div g T, abs_of_pos hT, smul_eq_mul]
  rw [hg, Commons.Analysis.Fourier.integral_tri_cos]
  rw [show Real.pi * (T * (d : ℝ)) = Real.pi * (d : ℝ) * T by ring]
  ring

/-- If `f` vanishes on `|u| ≥ 1/2` then its interval integral over `(-1/2, 1/2)` is its
integral over `ℝ`. -/
lemma intervalIntegral_eq_integral_of_zero_of_half_le_abs {f : ℝ → ℝ}
    (h : ∀ u : ℝ, 1 / 2 ≤ |u| → f u = 0) :
    ∫ u in (-(1 / 2) : ℝ)..(1 / 2), f u = ∫ u : ℝ, f u := by
  have hpt : ∀ u : ℝ, f u = (Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator f u := by
    intro u
    by_cases hu : u ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      exact h u (by
        simp only [Set.mem_Icc, not_and_or, not_le] at hu
        rcases hu with hu | hu
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith)
  calc ∫ u in (-(1 / 2) : ℝ)..(1 / 2), f u
      = ∫ u in Set.Ioc (-(1 / 2) : ℝ) (1 / 2), f u :=
        intervalIntegral.integral_of_le (by norm_num)
    _ = ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), f u :=
        (MeasureTheory.integral_Icc_eq_integral_Ioc).symm
    _ = ∫ u : ℝ, (Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator f u :=
        (MeasureTheory.integral_indicator measurableSet_Icc).symm
    _ = ∫ u : ℝ, f u := by
        rw [show (fun u : ℝ => (Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator f u) = f from
          funext fun u => (hpt u).symm]

theorem tent_cos_integral {T : ℝ} (hT : 0 < T) (hT2 : T ≤ 1 / 2) (d : ℤ) :
    ∫ u in (-(1 / 2) : ℝ)..(1 / 2), tent T u * Real.cos (2 * Real.pi * (d : ℝ) * u)
      = if d = 0 then T ^ 2 else (Real.sin (Real.pi * (d : ℝ) * T)) ^ 2 / (Real.pi * (d : ℝ)) ^ 2 := by
  have hzero : ∀ u : ℝ, 1 / 2 ≤ |u| →
      tent T u * Real.cos (2 * Real.pi * (d : ℝ) * u) = 0 := by
    intro u hu
    rw [tent_eq_zero_of_le (le_trans hT2 hu), zero_mul]
  rw [intervalIntegral_eq_integral_of_zero_of_half_le_abs hzero, integral_tent_cos hT d]
  rcases eq_or_ne d 0 with hd | hd
  · subst hd
    simp
  · rw [if_neg hd]
    have hdR : (d : ℝ) ≠ 0 := by
      intro h
      exact hd (by exact_mod_cast h)
    have hx : Real.pi * (d : ℝ) * T ≠ 0 :=
      mul_ne_zero (mul_ne_zero Real.pi_ne_zero hdR) (ne_of_gt hT)
    rw [Real.sinc_of_ne_zero hx, div_pow]
    field_simp

end

end Work.GM.Affine
