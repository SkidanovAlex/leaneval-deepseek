import Mathlib

namespace Work.TMComp.RedProj

open Complex MeasureTheory intervalIntegral Set

/-- Auxiliary contour-deformation lemma: for a function holomorphic on the strip
`{|im w| < ρ}` and invariant under `w ↦ w + 1`, the integral over the horizontal
segment `[0,1]` is unchanged when the segment is shifted to height `s`. -/
private lemma aux_horiz (f : ℂ → ℂ) (ρ : ℝ)
    (hdiff : DifferentiableOn ℂ f {w : ℂ | |w.im| < ρ})
    (hper : ∀ w : ℂ, |w.im| < ρ → f (w + 1) = f w)
    (s : ℝ) (hs : |s| < ρ) :
    (∫ x in (0:ℝ)..1, f (x : ℂ)) = ∫ x in (0:ℝ)..1, f ((x : ℂ) + (s : ℂ) * Complex.I) := by
  have hd : DifferentiableOn ℂ f (uIcc (0:ℝ) 1 ×ℂ uIcc (0:ℝ) s) := by
    refine hdiff.mono ?_
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    obtain ⟨h1, h2⟩ := hw
    have : |w.im| ≤ |s| := by
      rw [Set.mem_uIcc] at h2
      rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
      · rw [abs_of_nonneg h2a]; exact le_trans h2b (le_abs_self s)
      · rw [abs_of_nonpos h2b]; exact le_trans (neg_le_neg h2a) (neg_le_abs s)
    exact lt_of_le_of_lt this hs
  have hd' : DifferentiableOn ℂ f
      (uIcc (0:ℂ).re (1 + (s:ℂ) * Complex.I).re ×ℂ uIcc (0:ℂ).im (1 + (s:ℂ)*Complex.I).im) := by
    simpa using hd
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (0 : ℂ) (1 + (s:ℂ)*Complex.I) hd'
  have hrect' : ((∫ x in (0:ℝ)..1, f (x:ℂ)) - (∫ x in (0:ℝ)..1, f ((x:ℂ) + (s:ℂ)*Complex.I))) +
      Complex.I • (∫ y in (0:ℝ)..s, f ((1:ℂ) + (y:ℂ)*Complex.I)) -
      Complex.I • (∫ y in (0:ℝ)..s, f ((y:ℂ)*Complex.I)) = 0 := by
    simpa using hrect
  have hV' : (∫ y in (0:ℝ)..s, f ((1:ℂ) + (y:ℂ)*Complex.I)) = (∫ y in (0:ℝ)..s, f ((y:ℂ)*Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    show f ((1:ℂ) + (y:ℂ)*Complex.I) = f ((y:ℂ)*Complex.I)
    have hyabs : |y| ≤ |s| := by
      rw [Set.mem_uIcc] at hy
      rcases hy with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [abs_of_nonneg ha]; exact le_trans hb (le_abs_self s)
      · rw [abs_of_nonpos hb]; exact le_trans (neg_le_neg ha) (neg_le_abs s)
    have him : ((y:ℂ) * Complex.I).im = y := by simp
    have hper_y := hper ((y:ℂ) * Complex.I) (by rw [him]; exact lt_of_le_of_lt hyabs hs)
    rw [show (1:ℂ) + (y:ℂ)*Complex.I = (y:ℂ)*Complex.I + 1 by ring]
    exact hper_y
  have h := hrect'
  rw [hV', add_sub_cancel_right] at h
  exact sub_eq_zero.mp h

theorem integral_shift_eq_of_periodic_strip (Φ : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hΦ : DifferentiableOn ℂ Φ {w : ℂ | |w.im| < ρ})
    (hper : ∀ w : ℂ, |w.im| < ρ → Φ (w + 1) = Φ w)
    (k : ℤ) (s : ℝ) (hs : |s| < ρ) :
    (∫ x in (0:ℝ)..1, Φ (x : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ))))
      = ∫ x in (0:ℝ)..1, Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I))) := by
  let c0 : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)
  let g : ℂ → ℂ := fun w => Φ w * Complex.exp (-(c0 * w))
  have hexp_c0 : Complex.exp (-c0) = 1 := by
    have hcc : -c0 = ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      simp only [c0, Int.cast_neg]; ring
    rw [hcc]; exact Complex.exp_int_mul_two_pi_mul_I (-k)
  have hg_diff : DifferentiableOn ℂ g {w : ℂ | |w.im| < ρ} := by
    have hE : Differentiable ℂ (fun w : ℂ => Complex.exp (-(c0 * w))) :=
      Complex.differentiable_exp.comp (((differentiable_const c0).mul differentiable_id).neg)
    exact hΦ.mul (hE.differentiableOn.mono (Set.subset_univ _))
  have hg_per : ∀ w : ℂ, |w.im| < ρ → g (w + 1) = g w := by
    intro w hw
    simp only [g]
    rw [hper w hw]
    congr 1
    rw [show -(c0 * (w + 1)) = -(c0 * w) + (-c0) by ring, Complex.exp_add, hexp_c0, mul_one]
  have h := aux_horiz g ρ hg_diff hg_per s hs
  simpa only [g, c0] using h

end Work.TMComp.RedProj
