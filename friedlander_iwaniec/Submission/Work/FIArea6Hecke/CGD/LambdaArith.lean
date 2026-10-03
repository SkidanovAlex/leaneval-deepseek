/-
# `Work.FIArea6Hecke.CGD.LambdaArith`

Arithmetic purity lemma underlying the conductor Gauss-sum linear-algebra in area 6:
if `M ≠ 0` is a Gaussian integer not dividing `ξ`, then `|M|²` cannot divide *both* the
real and the imaginary parts of `M · conj ξ`.

Equivalently, writing `z = M · conj ξ`, at least one of the two integers
`Re z = gdot M ξ` and `Im z = gdot (star i · M) ξ` fails to be divisible by
`N = gnorm M = |M|²`.

The content is the observation `N | M · conj ξ ⟺ M | ξ`: since `N = M · conj M`, the
integer `N` divides `M · conj ξ` exactly when `conj M` divides `conj ξ`, i.e. (applying
conjugation) when `M` divides `ξ`.  Because an integer divides a Gaussian integer iff it
divides both coordinates, if `N` divided both `Re z` and `Im z` then `N | z`, forcing
`M | ξ`, contrary to hypothesis.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.ConductorGaussSumDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke.CGD

open Work.FIArea6Hecke.R

/-- If `M.norm : ℤ` divides both coordinates of a Gaussian integer `z`, then the Gaussian
integer `M.norm` divides `z`.  (`M.norm` is a nonnegative integer, i.e. a rational-prime-free
"scalar" inside `ℤ[i]`.) -/
lemma intCast_norm_dvd_of_dvd_re_im (M z : GaussianInt)
    (h1 : (M.norm : ℤ) ∣ z.re) (h2 : (M.norm : ℤ) ∣ z.im) :
    ((M.norm : ℤ) : GaussianInt) ∣ z := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨⟨a, b⟩, ?_⟩
  ext
  · simp [ha]
  · simp [hb]

theorem LambdaArith (M ξ : GaussianInt) (hM : M ≠ 0) (hξ : ¬ M ∣ ξ) :
    ¬ (Work.FIPlan.gnorm M : ℤ) ∣ Work.FIArea6Hecke.R.gdot M ξ ∨
      ¬ (Work.FIPlan.gnorm M : ℤ) ∣
        Work.FIArea6Hecke.R.gdot (star (⟨0, 1⟩ : GaussianInt) * M) ξ := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨h1, h2⟩ := h
  -- `gnorm M = M.norm` as integers.
  have hN : (Work.FIPlan.gnorm M : ℤ) = M.norm := GaussianInt.abs_natCast_norm M
  rw [hN] at h1 h2
  -- Identify the two `gdot` values with the coordinates of `z = M * conj ξ`.
  have hzre : (M * star ξ).re = Work.FIArea6Hecke.R.gdot M ξ := by
    simp only [Work.FIArea6Hecke.R.gdot, Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]
    ring
  have hzim : (M * star ξ).im =
      Work.FIArea6Hecke.R.gdot (star (⟨0, 1⟩ : GaussianInt) * M) ξ := by
    simp only [Work.FIArea6Hecke.R.gdot, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.star_mk,
      Zsqrtd.re_star, Zsqrtd.im_star]
    ring
  have hdiv1 : (M.norm : ℤ) ∣ (M * star ξ).re := by rw [hzre]; exact h1
  have hdiv2 : (M.norm : ℤ) ∣ (M * star ξ).im := by rw [hzim]; exact h2
  -- Both coordinates divisible by the integer `N = M.norm` forces `N ∣ z`.
  have hdivstar : ((M.norm : ℤ) : GaussianInt) ∣ M * star ξ :=
    intCast_norm_dvd_of_dvd_re_im M (M * star ξ) hdiv1 hdiv2
  -- `N = M * conj M`.
  have hnorm : ((M.norm : ℤ) : GaussianInt) = M * star M := Zsqrtd.norm_eq_mul_conj M
  rw [hnorm] at hdivstar
  -- Cancel the factor `M` (nonzero): `conj M ∣ conj ξ`.
  have hc : star M ∣ star ξ := (mul_dvd_mul_iff_left hM).mp hdivstar
  obtain ⟨c, hc'⟩ := hc
  -- Conjugating back gives `M ∣ ξ`, contradicting `hξ`.
  exact hξ ⟨star c, by
    have hstar := congrArg star hc'
    simp only [star_mul, star_star] at hstar
    rw [hstar, mul_comm]⟩

end Work.FIArea6Hecke.CGD
