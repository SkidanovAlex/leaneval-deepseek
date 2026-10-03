/-
# `Work.FIArea7.absDelta_ne_zero_of_isCoprime`

If `z₁, z₂ ∈ ℤ[i]` are coprime and `z₁` has both coordinates non-zero, then the determinant
`Δ(z₁,z₂) = Im(z̄₁ z₂) = r₁s₂ - r₂s₁` of the paper (6.1) does not vanish.

The argument is elementary.  `Δ(z₁,z₂) = 0` says that `(r₁,s₁)` and `(r₂,s₂)` are proportional
over `ℚ`; read in `ℤ[i]` this is the identity `s₁ · z₂ = s₂ · z₁` (`sᵢ = Im zᵢ`).  Since
`z₁ ∣ s₂ z₁` trivially, Euclid's lemma for the coprime pair `(z₁,z₂)` gives `z₁ ∣ s₁ = Im z₁`.
Passing to the norm `|w|² = (Re w)² + (Im w)²`, this says `|z₁|² = r₁² + s₁²` divides `s₁²`, which
is impossible since `s₁ ≠ 0` and `r₁ ≠ 0` force `s₁² < r₁² + s₁²`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea1.Basic

set_option autoImplicit false

namespace Work.FIArea7

/-- `Δ(z₁,z₂) = r₁s₂ - r₂s₁` in coordinates (paper (6.1)). -/
lemma delta_eq_coords (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z1.im * z2.re := by
  unfold Work.FIPlan.Delta
  rw [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- **Proportionality.**  Vanishing of `Δ` means that `z₁` and `z₂` are proportional over `ℚ`; in
`ℤ[i]` this reads `Im z₁ · z₂ = Im z₂ · z₁`. -/
lemma im_mul_eq_of_delta_eq_zero {z1 z2 : GaussianInt}
    (hD : Work.FIPlan.Delta z1 z2 = 0) :
    (((z1.im : ℤ)) : GaussianInt) * z2 = (((z2.im : ℤ)) : GaussianInt) * z1 := by
  have hcoords : z1.im * z2.re = z2.im * z1.re := by
    have h : z1.re * z2.im - z1.im * z2.re = 0 := by
      rw [← delta_eq_coords]
      exact hD
    have h1 : z1.re * z2.im = z1.im * z2.re := by linarith
    calc z1.im * z2.re = z1.re * z2.im := h1.symm
      _ = z2.im * z1.re := by ring
  apply Zsqrtd.ext
  · simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
    rw [hcoords]
    ring
  · simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
    ring

/-- **`Δ` does not vanish on a coprime pair** whose first member has both coordinates non-zero
(paper §6: `Δ(z₁,z₂) = 0` means the two Gaussian integers are proportional, hence share a
non-trivial common divisor). -/
theorem absDelta_ne_zero_of_isCoprime {z1 z2 : GaussianInt}
    (hc : IsCoprime z1 z2) (hre : z1.re ≠ 0) (him : z1.im ≠ 0) :
    Work.FIPlan.Delta z1 z2 ≠ 0 := by
  intro hD
  -- Euclid's lemma in `ℤ[i]`: from `s₁ z₂ = s₂ z₁` and coprimality, `z₁ ∣ s₁ = Im z₁`.
  have hdvd : z1 ∣ (((z1.im : ℤ)) : GaussianInt) := by
    have h0 : z1 ∣ (((z2.im : ℤ)) : GaussianInt) * z1 := dvd_mul_left z1 _
    rw [← im_mul_eq_of_delta_eq_zero hD] at h0
    exact IsCoprime.dvd_of_dvd_mul_right hc h0
  -- hence `|z₁|² ∣ (Im z₁)²`
  have hgn : Work.FIPlan.gnorm z1 ∣ z1.im.natAbs ^ 2 := by
    have hgs : Work.FIPlan.gnorm z1 ∣ Work.FIPlan.gnorm (((z1.im : ℤ)) : GaussianInt) := by
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, Work.FIArea1.gnorm_mul]
      exact dvd_mul_right _ _
    rwa [Work.FIArea1.gnorm_intCast] at hgs
  -- but `(Im z₁)² < (Re z₁)² + (Im z₁)² = |z₁|²`, since `Re z₁ ≠ 0`
  have hpos : 0 < z1.im.natAbs ^ 2 :=
    pow_pos (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr him)) 2
  have hle : Work.FIPlan.gnorm z1 ≤ z1.im.natAbs ^ 2 := Nat.le_of_dvd hpos hgn
  rw [Work.FIArea1.gnorm_coords] at hle
  have hposre : 0 < z1.re.natAbs ^ 2 :=
    pow_pos (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hre)) 2
  omega

end Work.FIArea7
