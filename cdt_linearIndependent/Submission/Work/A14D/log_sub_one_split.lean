import Mathlib

/-!
# `Work.A14D.log_sub_one_split`

The two half-plane versions of `log (-w) = log w ± π i` for the principal branch `Complex.log`:

for `w` in the open upper half-plane, `log w = log (-w) + π i`;
for `w` in the open lower half-plane, `log w = log (-w) - π i`.

Specialising `w = z - 1` (so that `-w = 1 - z`) gives the requested statement: crossing the
branch cut of `log` along the segment `(-∞, 0)` costs `+π i` from above and `-π i` from below.

The proof is `Complex.ext` on real and imaginary parts: the real part is `Real.log ‖w‖` on both
sides (`‖-w‖ = ‖w‖`), while the imaginary parts are the arguments, related by
`Complex.arg_neg_eq_arg_sub_pi_of_im_pos` resp. `Complex.arg_neg_eq_arg_add_pi_of_im_neg`.
-/

namespace Work.A14D

/-- For `w` in the open upper half-plane, `log w = log (-w) + π i`. -/
private lemma log_eq_log_neg_add_pi_mul_I (w : ℂ) (h : 0 < w.im) :
    Complex.log w = Complex.log (-w) + Real.pi * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]

/-- For `w` in the open lower half-plane, `log w = log (-w) - π i`. -/
private lemma log_eq_log_neg_sub_pi_mul_I (w : ℂ) (h : w.im < 0) :
    Complex.log w = Complex.log (-w) - Real.pi * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg h]

theorem log_sub_one_split (z : ℂ) :
    (0 < z.im → Complex.log (z - 1) = Complex.log (1 - z) + Real.pi * Complex.I) ∧
    (z.im < 0 → Complex.log (z - 1) = Complex.log (1 - z) - Real.pi * Complex.I) := by
  constructor
  · intro hz
    have him : 0 < ((z - 1 : ℂ)).im := by simpa using hz
    have h := log_eq_log_neg_add_pi_mul_I (z - 1) him
    have h1z : -(z - 1) = (1 : ℂ) - z := by ring
    rwa [h1z] at h
  · intro hz
    have him : ((z - 1 : ℂ)).im < 0 := by simpa using hz
    have h := log_eq_log_neg_sub_pi_mul_I (z - 1) him
    have h1z : -(z - 1) = (1 : ℂ) - z := by ring
    rwa [h1z] at h

end Work.A14D
