import Mathlib

namespace Work.ZeroFreeTables.XY

/-- The recursive evaluation of `(x + t·i)^n` inside `ℂ`. -/
private def powC (x t : ℝ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => powC x t n * ((x:ℂ) + (t:ℂ)*Complex.I)

private lemma powC_spec (x t : ℝ) (n : ℕ) :
    ((x:ℂ) + (t:ℂ)*Complex.I)^n = powC x t n := by
  induction n with
  | zero => simp [powC]
  | succ k ih => rw [pow_succ, ih]; rfl

private lemma re_pow (x t : ℝ) (n : ℕ) :
    (((x:ℂ) + (t:ℂ)*Complex.I)^n).re = (powC x t n).re := by rw [powC_spec]

private lemma im_pow (x t : ℝ) (n : ℕ) :
    (((x:ℂ) + (t:ℂ)*Complex.I)^n).im = (powC x t n).im := by rw [powC_spec]

private lemma hns (x t : ℝ) (n : ℕ) :
    Complex.normSq (((x:ℂ) + (t:ℂ)*Complex.I)^n) = (x^2+t^2)^n := by
  have hz : Complex.normSq ((x:ℂ) + (t:ℂ)*Complex.I) = x^2 + t^2 := by
    simp [Complex.normSq_apply]
    ring
  rw [map_pow, hz]

theorem XyInvPowReIm (x t : ℝ) (hxt : x^2 + t^2 ≠ 0) :
    (((((x:ℂ) + (t:ℂ)*Complex.I))⁻¹).re = x/(x^2+t^2))
    ∧ (((((x:ℂ) + (t:ℂ)*Complex.I)^3)⁻¹).re = (x^3-3*x*t^2)/(x^2+t^2)^3)
    ∧ (((((x:ℂ) + (t:ℂ)*Complex.I)^4)⁻¹).re = (x^4-6*x^2*t^2+t^4)/(x^2+t^2)^4)
    ∧ (((((x:ℂ) + (t:ℂ)*Complex.I)^4)⁻¹).im = (4*x*t^3-4*x^3*t)/(x^2+t^2)^4)
    ∧ (((((x:ℂ) + (t:ℂ)*Complex.I)^5)⁻¹).re = (x^5-10*x^3*t^2+5*x*t^4)/(x^2+t^2)^5)
    ∧ (((((x:ℂ) + (t:ℂ)*Complex.I)^5)⁻¹).im = (10*x^2*t^3-5*x^4*t-t^5)/(x^2+t^2)^5)
    ∧ (((((x:ℂ) + (t:ℂ)*Complex.I)^6)⁻¹).re = (x^6-15*x^4*t^2+15*x^2*t^4-t^6)/(x^2+t^2)^6)
    ∧ (((((x:ℂ) + (t:ℂ)*Complex.I)^6)⁻¹).im = (20*x^3*t^3-6*x^5*t-6*x*t^5)/(x^2+t^2)^6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Complex.inv_re]
    simp [Complex.normSq_apply]
    ring
  · rw [Complex.inv_re, hns, re_pow]
    simp [powC]
    ring
  · rw [Complex.inv_re, hns, re_pow]
    simp [powC]
    ring
  · rw [Complex.inv_im, hns, im_pow]
    simp [powC]
    ring
  · rw [Complex.inv_re, hns, re_pow]
    simp [powC]
    ring
  · rw [Complex.inv_im, hns, im_pow]
    simp [powC]
    ring
  · rw [Complex.inv_re, hns, re_pow]
    simp [powC]
    ring
  · rw [Complex.inv_im, hns, im_pow]
    simp [powC]
    ring

end Work.ZeroFreeTables.XY
