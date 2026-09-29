import Mathlib
import Submission.Work.Fx.scaleCommon

/-!
# Truncation error of `Int.tdiv` by a positive integer (`< √2` in the Gaussian metric)

Requested lemma for the `Fx` area. For integers `A B : ℤ` and `b : ℕ`, `b > 0`, the Gaussian
integer `(A.tdiv b) + (B.tdiv b) i` approximates the point `(A + B i)/b` of the complex plane
with error `< √2`: indeed each coordinate is `-c/b` with `c = A.tmod b` (resp. `B.tmod b`),
`|c| < b`, so each coordinate of the error has absolute value `< 1` and the squared norm is
`< 1 + 1 = 2`.
-/

set_option autoImplicit false

namespace Work.Fx

/-- The remainder of a truncating division by a positive integer has modulus `< b`. -/
private theorem abs_tmod_lt_x2 (A : ℤ) {b : ℤ} (hb : 0 < b) : |A.tmod b| < b := by
  rw [abs_lt]
  exact ⟨Int.lt_tmod_of_pos A hb, Int.tmod_lt_of_pos A hb⟩

/-- Rounding towards zero: `|A.tdiv b - A/b| < 1` for `b > 0` (as real numbers). -/
private theorem abs_tdiv_sub_div_lt_one (A : ℤ) {b : ℕ} (hb : 0 < b) :
    |((A.tdiv (b : ℤ) : ℤ) : ℝ) - (A : ℝ) / (b : ℝ)| < 1 := by
  have hbZ : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hdec := Int.tmod_add_tdiv_mul A (b : ℤ)
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hsplit : (A : ℝ) / (b : ℝ)
      = ((A.tdiv (b : ℤ) : ℤ) : ℝ) + ((A.tmod (b : ℤ) : ℤ) : ℝ) / (b : ℝ) := by
    have h : ((A.tmod (b : ℤ) : ℤ) : ℝ) + ((A.tdiv (b : ℤ) : ℤ) : ℝ) * (b : ℝ) = (A : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hdec
      push_cast at this
      linarith [this]
    field_simp
    linarith [h]
  have hkey : ((A.tdiv (b : ℤ) : ℤ) : ℝ) - (A : ℝ) / (b : ℝ)
      = -(((A.tmod (b : ℤ) : ℤ) : ℝ) / (b : ℝ)) := by
    rw [hsplit]; ring
  rw [hkey, abs_neg, abs_div, abs_of_pos hbR, div_lt_one hbR, ← Int.cast_abs]
  exact_mod_cast abs_tmod_lt_x2 A hbZ

/-- Truncating division of the two components of a Gaussian integer by `b` moves the value
`(A + Bi)/b` by less than `√2`: each coordinate changes by `< 1`. -/
theorem norm_tdiv_sub_div_lt {A B : ℤ} {b : ℕ} (hb : 0 < b) :
    ‖((Int.tdiv A b : ℤ) : ℂ) + ((Int.tdiv B b : ℤ) : ℂ) * Complex.I
        - (((A : ℝ) + (B : ℝ) * Complex.I) / (b : ℂ))‖ < Real.sqrt 2 := by
  set z : ℂ := ((Int.tdiv A b : ℤ) : ℂ) + ((Int.tdiv B b : ℤ) : ℂ) * Complex.I
        - (((A : ℝ) + (B : ℝ) * Complex.I) / (b : ℂ)) with hz
  have hzre : z.re = ((A.tdiv (b : ℤ) : ℤ) : ℝ) - (A : ℝ) / (b : ℝ) := by
    rw [hz]
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
  have hzim : z.im = ((B.tdiv (b : ℤ) : ℤ) : ℝ) - (B : ℝ) / (b : ℝ) := by
    rw [hz]
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
  have hx : |z.re| < 1 := by rw [hzre]; exact abs_tdiv_sub_div_lt_one A hb
  have hy : |z.im| < 1 := by rw [hzim]; exact abs_tdiv_sub_div_lt_one B hb
  have hx2 : z.re ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one z.re).2 hx
  have hy2 : z.im ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one z.im).2 hy
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [Real.lt_sqrt (norm_nonneg z), hsq]
  linarith

end Work.Fx
