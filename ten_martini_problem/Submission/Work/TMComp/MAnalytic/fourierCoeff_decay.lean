import Mathlib

open MeasureTheory Set intervalIntegral
open scoped Interval

namespace Work.TMComp.MAnalytic

/-- If `y` lies between `0` and `a`, then `|y| ≤ |a|`. -/
private lemma abs_le_abs_of_mem_uIcc_zero {a y : ℝ} (hy : y ∈ [[(0:ℝ), a]]) : |y| ≤ |a| := by
  rcases le_total 0 a with ha | ha
  · rw [Set.uIcc_of_le ha, Set.mem_Icc] at hy
    rw [abs_of_nonneg hy.1, abs_of_nonneg ha]
    exact hy.2
  · rw [Set.uIcc_of_ge ha, Set.mem_Icc] at hy
    rw [abs_of_nonpos hy.2, abs_of_nonpos ha]
    linarith [hy.1]

/-- Cauchy–Goursat on the rectangle with corners `0` and `1 + s·I`, written in the
specific shape used below. -/
private theorem rect_boundary_eq_zero {f : ℂ → ℂ} {s : ℝ}
    (hfd : DifferentiableOn ℂ f ([[(0:ℝ),1]] ×ℂ [[(0:ℝ), s]])) :
    (∫ x in (0:ℝ)..1, f (x : ℂ))
      - (∫ x in (0:ℝ)..1, f ((x : ℂ) + (s : ℂ) * Complex.I))
      + Complex.I • (∫ y in (0:ℝ)..s, f ((1:ℂ) + (y : ℂ) * Complex.I))
      - Complex.I • (∫ y in (0:ℝ)..s, f ((y : ℂ) * Complex.I)) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (0:ℂ) (⟨1, s⟩ : ℂ) hfd
  convert h using 2 <;> simp

/-- Contour shift for a periodic function holomorphic on a horizontal strip:
integrating over `[0,1]` at height `0` equals integrating at any height `s` with `|s| < ρ`. -/
private theorem integral_shift_eq_of_periodic_strip {ρ s : ℝ} {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f ([[(0:ℝ),1]] ×ℂ [[(0:ℝ), s]]))
    (hper : ∀ x : ℂ, |x.im| < ρ → f (x + 1) = f x)
    (hs : |s| < ρ) :
    (∫ x in (0:ℝ)..1, f (x : ℂ)) = ∫ x in (0:ℝ)..1, f ((x : ℂ) + (s : ℂ) * Complex.I) := by
  have h := rect_boundary_eq_zero (f := f) (s := s) hfd
  have hvert : (∫ y in (0:ℝ)..s, f ((1:ℂ) + (y : ℂ) * Complex.I))
      = (∫ y in (0:ℝ)..s, f ((y : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hyabs : |y| ≤ |s| := abs_le_abs_of_mem_uIcc_zero hy
    have hylt : |y| < ρ := lt_of_le_of_lt hyabs hs
    have h1 := hper ((y : ℂ) * Complex.I) (by simpa using hylt)
    simpa [add_comm] using h1
  have h2 : (∫ x in (0:ℝ)..1, f (x : ℂ))
      - (∫ x in (0:ℝ)..1, f ((x : ℂ) + (s : ℂ) * Complex.I)) = 0 := by
    have h' := h
    rw [hvert] at h'
    simpa using h'
  exact sub_eq_zero.mp h2

theorem fourierCoeff_decay {δ : ℝ} (hδ : 0 < δ) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g {x : ℂ | |x.im| < δ}) (hper : ∀ x, g (x + 1) = g x) {B : ℝ}
    (hB : ∀ x, |x.im| < δ → ‖g x‖ ≤ B) {r : ℝ} (hr : 0 < r) (hrδ : r < δ) (k : ℤ) :
    ‖∫ t in (0 : ℝ)..1, g (t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ)))‖
      ≤ B * Real.exp (-(2 * Real.pi * |(k : ℝ)| * r)) := by
  set h : ℂ → ℂ := fun z => g z * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * z)) with hh
  have hexp1 : Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ))) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨-k, by push_cast; ring⟩
  have hperh : ∀ z : ℂ, |z.im| < δ → h (z + 1) = h z := by
    intro z _
    simp only [hh]
    rw [hper z]
    have harg : (-(2 * Real.pi * Complex.I * (k : ℂ) * (z + 1)))
        = (-(2 * Real.pi * Complex.I * (k : ℂ) * z)) + (-(2 * Real.pi * Complex.I * (k : ℂ))) := by
      ring
    rw [harg, Complex.exp_add, hexp1, mul_one]
  have hdiff : DifferentiableOn ℂ h {x : ℂ | |x.im| < δ} := by
    have hgd : DifferentiableOn ℂ g {x : ℂ | |x.im| < δ} := hg.differentiableOn
    have hed : DifferentiableOn ℂ
        (fun z : ℂ => Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * z))) Set.univ :=
      (by fun_prop : Differentiable ℂ
        (fun z : ℂ => Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * z)))).differentiableOn
    simp only [hh]
    exact hgd.mul (hed.mono (Set.subset_univ _))
  have key : ∀ s : ℝ, |s| < δ → 2 * Real.pi * (k : ℝ) * s = -(2 * Real.pi * |(k : ℝ)| * r) →
      ‖∫ t in (0:ℝ)..1, h (t : ℂ)‖ ≤ B * Real.exp (-(2 * Real.pi * |(k : ℝ)| * r)) := by
    intro s hs harg
    have hrect : DifferentiableOn ℂ h ([[(0:ℝ),1]] ×ℂ [[(0:ℝ), s]]) := by
      apply hdiff.mono
      intro z hz
      have him : z.im ∈ [[(0:ℝ), s]] := ((Complex.mem_reProdIm).mp hz).2
      exact lt_of_le_of_lt (abs_le_abs_of_mem_uIcc_zero him) hs
    have hshift := integral_shift_eq_of_periodic_strip (ρ := δ) (s := s) hrect hperh hs
    have hpoint : ∀ t : ℝ,
        ‖h ((t : ℂ) + (s : ℂ) * Complex.I)‖ ≤ B * Real.exp (2 * Real.pi * (k : ℝ) * s) := by
      intro t
      have hzs : |((t : ℂ) + (s : ℂ) * Complex.I).im| < δ := by
        have : ((t : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
        rw [this]; exact hs
      have hgt : ‖g ((t : ℂ) + (s : ℂ) * Complex.I)‖ ≤ B := hB _ hzs
      have hex : ‖Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ)
            * ((t : ℂ) + (s : ℂ) * Complex.I)))‖ = Real.exp (2 * Real.pi * (k : ℝ) * s) := by
        rw [Complex.norm_exp]
        congr 1
        simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im]
        norm_num
      simp only [hh]
      rw [norm_mul, hex]
      exact mul_le_mul_of_nonneg_right hgt (Real.exp_pos _).le
    calc ‖∫ t in (0:ℝ)..1, h (t : ℂ)‖
        = ‖∫ t in (0:ℝ)..1, h ((t : ℂ) + (s : ℂ) * Complex.I)‖ := by rw [hshift]
      _ ≤ B * Real.exp (2 * Real.pi * (k : ℝ) * s) := by
            have hb : ‖∫ t in (0:ℝ)..1, h ((t : ℂ) + (s : ℂ) * Complex.I)‖
                ≤ (B * Real.exp (2 * Real.pi * (k : ℝ) * s)) * |(1:ℝ) - 0| :=
              intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hpoint t)
            rw [sub_zero, abs_one, mul_one] at hb
            exact hb
      _ = B * Real.exp (-(2 * Real.pi * |(k : ℝ)| * r)) := by rw [harg]
  have keyapplied : ‖∫ t in (0:ℝ)..1, h (t : ℂ)‖ ≤ B * Real.exp (-(2 * Real.pi * |(k : ℝ)| * r)) := by
    by_cases hk : (0:ℤ) ≤ k
    · refine key (-r) (by rw [abs_neg, abs_of_pos hr]; exact hrδ) ?_
      rw [abs_of_nonneg (by exact_mod_cast hk)]
      ring
    · push_neg at hk
      refine key r (by rw [abs_of_pos hr]; exact hrδ) ?_
      rw [abs_of_neg (by exact_mod_cast hk)]
      ring
  simpa only [hh] using keyapplied

end Work.TMComp.MAnalytic
