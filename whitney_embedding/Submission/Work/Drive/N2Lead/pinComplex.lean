import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi

/-!
# The complex bookkeeping of the saddle pin arcs

Two points of the anchor level `Re z² = -ηs` and of the upper level `Re z² = +ηs` with the same
imaginary part `w = Im z²` are related by the collar flow of the model.  The identification of the
image of an upper point under the model map `saddlePsi` (which is what the collar row computes, see
`Work.Drive.N2.saddlePsi_collar`) with one of the two anchor points works through the *sign* of
`Re (u * conj z)`: this file proves, in closed form,

* `sq_eq_sqrt_or` — a square root of `c ≠ 0` is `± √c`;
* `conj_sqrt_ofReal_add_mul_I` — `conj (√(a + i w)) = √(a - i w)` for `a ≥ 0` (the principal square
  root of a complex number with nonnegative real part commutes with conjugation);
* `re_I_sqrt_mul_conj` — `Re (I * √(a - i w) * conj (√(a + i w))) = w`;
* `sqrt_re_pos` — the principal square root of a number with positive real part has positive real
  part;
* `collar_anchor_eq` — **the identification**: if `z² = a + i w` and `u² = -a + i w` (with `a > 0`,
  `w ≠ 0`), then `Re (u * conj z) > 0` forces
  `u = sgn(w) * sgn(Re z) * (I * √(a - i w))`.
-/

namespace Work.Drive.N2Lead

open Complex

/-- A square root of `c ≠ 0` is `± √c` (the principal square root). -/
lemma sq_eq_sqrt_or {c : ℂ} (hc : c ≠ 0) {x : ℂ} (hx : x ^ 2 = c) :
    x = Complex.sqrt c ∨ x = - Complex.sqrt c := by
  have hs : Complex.sqrt c ^ 2 = c := Work.Drive.N2.complex_sqrt_sq c
  have h2 : x ^ 2 = Complex.sqrt c ^ 2 := by rw [hx, hs]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The principal square root of a complex number with positive real part has positive real part. -/
lemma sqrt_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < (Complex.sqrt z).re := by
  show 0 < (z ^ (2⁻¹ : ℂ)).re
  rw [Complex.cpow_inv_two_re]
  apply Real.sqrt_pos_of_pos
  have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  rw [abs_of_pos hz] at h1
  linarith

/-- **Conjugation commutes with the principal square root** for `a ≥ 0`
(`√(a + i w)` and `√(a - i w)` are conjugate). -/
lemma conj_sqrt_ofReal_add_mul_I {a : ℝ} (ha : 0 ≤ a) (w : ℝ) :
    (starRingEnd ℂ) (Complex.sqrt ((a:ℂ) + (w:ℂ)*Complex.I))
    = Complex.sqrt ((a:ℂ) - (w:ℂ)*Complex.I) := by
  have hnorm : ‖(a:ℂ) + (w:ℂ)*Complex.I‖ = ‖(a:ℂ) - (w:ℂ)*Complex.I‖ := by
    have h : ‖(a:ℂ) + (w:ℂ)*Complex.I‖^2 = ‖(a:ℂ) - (w:ℂ)*Complex.I‖^2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, Complex.sub_re, Complex.sub_im,
        zero_sub, neg_mul, add_zero, Complex.add_im, Complex.mul_im]
      ring
    nlinarith [norm_nonneg ((a:ℂ) + (w:ℂ)*Complex.I), norm_nonneg ((a:ℂ) - (w:ℂ)*Complex.I), h]
  rcases lt_trichotomy w 0 with hw | hw | hw
  · rw [Complex.sqrt_eq_real_add_ite, Complex.sqrt_eq_real_add_ite]
    have hre1 : ((a:ℂ) + (w:ℂ)*Complex.I).re = a := by simp
    have hre2 : ((a:ℂ) - (w:ℂ)*Complex.I).re = a := by simp
    have him1 : ((a:ℂ) + (w:ℂ)*Complex.I).im = w := by simp
    have him2 : ((a:ℂ) - (w:ℂ)*Complex.I).im = -w := by simp
    rw [hre1, hre2, him1, him2, hnorm, if_neg (by linarith : ¬ (0:ℝ) ≤ w),
      if_pos (by linarith : (0:ℝ) ≤ -w)]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_one, map_neg]
    ring
  · subst hw
    simp only [Complex.ofReal_zero, zero_mul, add_zero, sub_zero]
    rw [Complex.sqrt_of_nonneg (by simpa using ha)]
    simp
  · rw [Complex.sqrt_eq_real_add_ite, Complex.sqrt_eq_real_add_ite]
    have hre1 : ((a:ℂ) + (w:ℂ)*Complex.I).re = a := by simp
    have hre2 : ((a:ℂ) - (w:ℂ)*Complex.I).re = a := by simp
    have him1 : ((a:ℂ) + (w:ℂ)*Complex.I).im = w := by simp
    have him2 : ((a:ℂ) - (w:ℂ)*Complex.I).im = -w := by simp
    rw [hre1, hre2, him1, him2, hnorm, if_pos (by linarith : (0:ℝ) ≤ w),
      if_neg (by linarith : ¬ (0:ℝ) ≤ -w)]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_one, map_neg]
    ring

/-- `I * (a - i w) = w + i a`. -/
lemma I_mul_sub_mul_I {a w : ℝ} :
    Complex.I * ((a:ℂ) - (w:ℂ)*Complex.I) = (w:ℂ) + (a:ℂ)*Complex.I := by
  apply Complex.ext <;>
  · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.mul_im,
      zero_mul, mul_zero, sub_zero, mul_one]
    ring

/-- **The sign functional of the collar**: `Re (I √(a - i w) * conj (√(a + i w))) = w`. -/
lemma re_I_sqrt_mul_conj {a : ℝ} (ha : 0 ≤ a) (w : ℝ) :
    (Complex.I * Complex.sqrt ((a:ℂ) - (w:ℂ)*Complex.I)
      * (starRingEnd ℂ) (Complex.sqrt ((a:ℂ) + (w:ℂ)*Complex.I))).re = w := by
  rw [conj_sqrt_ofReal_add_mul_I ha w]
  have hsq : Complex.sqrt ((a:ℂ) - (w:ℂ)*Complex.I) * Complex.sqrt ((a:ℂ) - (w:ℂ)*Complex.I)
      = (a:ℂ) - (w:ℂ)*Complex.I := by
    simpa [pow_two] using Work.Drive.N2.complex_sqrt_sq ((a:ℂ) - (w:ℂ)*Complex.I)
  rw [mul_assoc, hsq, I_mul_sub_mul_I]
  simp

/-- **The identification of the collar anchor**: if `z² = a + i w` and `u² = -a + i w` with
`a > 0` and `w ≠ 0`, then the sign `Re (u * conj z) > 0` (which is what
`Work.Drive.N2.saddlePsi_collar` supplies for the model map `u = saddlePsi η δ z`) forces
`u = sgn (w) * sgn (Re z) * (I √(a - i w))` — i.e. `u` is the point of the anchor level whose
scaled coordinate flips the level and keeps the quadrant of `z`. -/
lemma collar_anchor_eq {a : ℝ} (ha : 0 < a) {w : ℝ} (_hw : w ≠ 0) {u z : ℂ}
    (hz : z ^ 2 = (a : ℂ) + (w : ℂ) * Complex.I)
    (hu : u ^ 2 = -(a : ℂ) + (w : ℂ) * Complex.I)
    (hsign : 0 < (u * (starRingEnd ℂ) z).re) :
    u = (if 0 < w then (1:ℂ) else -1) * (if 0 < z.re then (1:ℂ) else -1)
          * (Complex.I * Complex.sqrt ((a:ℂ) - (w:ℂ)*Complex.I)) := by
  set v : ℂ := Complex.sqrt ((a:ℂ) + (w:ℂ)*Complex.I) with hv
  set u₀ : ℂ := Complex.I * Complex.sqrt ((a:ℂ) - (w:ℂ)*Complex.I) with hu₀
  have hv2 : v ^ 2 = (a:ℂ) + (w:ℂ)*Complex.I := by
    rw [hv]; simpa [pow_two] using Work.Drive.N2.complex_sqrt_sq ((a:ℂ) + (w:ℂ)*Complex.I)
  have hu₀2 : u₀ ^ 2 = -(a:ℂ) + (w:ℂ)*Complex.I := by
    have h1 : Complex.sqrt ((a:ℂ) - (w:ℂ)*Complex.I) ^ 2 = (a:ℂ) - (w:ℂ)*Complex.I :=
      Work.Drive.N2.complex_sqrt_sq _
    rw [hu₀, mul_pow, h1, Complex.I_sq]
    ring
  have hvpos : 0 < v.re := by
    rw [hv]; exact sqrt_re_pos (by simpa using ha)
  have hucase : u = u₀ ∨ u = -u₀ := by
    have h : u ^ 2 = u₀ ^ 2 := by rw [hu, hu₀2]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h
  have hzcase : z = v ∨ z = -v := by
    have h : z ^ 2 = v ^ 2 := by rw [hz, hv2]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h
  have hkey1 : (u₀ * (starRingEnd ℂ) v).re = w := re_I_sqrt_mul_conj ha.le w
  have hnegv : ¬ (0:ℝ) < (-v).re := by simp only [Complex.neg_re]; linarith [hvpos]
  rcases hzcase with hz' | hz' <;> rcases hucase with hu' | hu'
  · have hwpos : 0 < w := by
      rw [hz', hu'] at hsign
      exact hkey1 ▸ hsign
    rw [hz', hu', if_pos hwpos, if_pos hvpos]
    ring
  · have hwneg : w < 0 := by
      have h2 : ((-u₀) * (starRingEnd ℂ) v).re = -w := by rw [neg_mul, Complex.neg_re, hkey1]
      rw [hz', hu', h2] at hsign
      linarith
    rw [hz', hu', if_neg (not_lt.mpr hwneg.le), if_pos hvpos]
    ring
  · have hwneg : w < 0 := by
      have h2 : (u₀ * (starRingEnd ℂ) (-v)).re = -w := by
        rw [map_neg, mul_neg, Complex.neg_re, hkey1]
      rw [hz', hu', h2] at hsign
      linarith
    rw [hz', hu', if_neg (not_lt.mpr hwneg.le), if_neg hnegv]
    ring
  · have hwpos : 0 < w := by
      have h2 : ((-u₀) * (starRingEnd ℂ) (-v)).re = w := by
        rw [map_neg, mul_neg, neg_mul, Complex.neg_re, Complex.neg_re, hkey1]
        ring
      rw [hz', hu', h2] at hsign
      exact hsign
    rw [hz', hu', if_pos hwpos, if_neg hnegv]
    ring

end Work.Drive.N2Lead
