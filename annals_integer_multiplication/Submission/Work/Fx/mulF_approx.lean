import Mathlib
import Submission.Work.Fx.FxLin

/-!
# The error analysis of the fixed-point complex product (paper Lemma 2.4)

`mulF_approx` is the arithmetic heart of Lemma 2.4 of Harvey–van der Hoeven: if two Gaussian
integers `(x,y)`, `(x',y')` lie in the disc `C̃◦ = {z : |z| ≤ 2^p}` (i.e. `inDisc p`), then the
componentwise truncation by `2^p` of their Gaussian product

`(X, Y) = ((x*x' - y*y').tdiv 2^p, (x*y' + y*x').tdiv 2^p)`

again lies in the disc, and the fixed point value `fxC p (X,Y) = 2^{-p}(X + iY)` approximates
`fxC p (x,y) * fxC p (x',y')` with error `ε = 2^p ‖·‖ < 2`.

The proofs are elementary:
* for the disc part, the truncation never increases a coordinate, so
  `X² + Y² ≤ (c² + d²)/4^p ≤ 4^p`, where `c² + d² = (x²+y²)(x'²+y'²) ≤ 4^p·4^p`
  is Lagrange's identity;
* for the error, `2^p (fxC p (X,Y) - fxC p (x,y) fxC p (x',y'))` equals
  `(X - c/2^p) + (Y - d/2^p) i` with `|X - c/2^p|, |Y - d/2^p| < 1` since truncating division
  has remainder of modulus `< 2^p`; hence the norm is `< 2`.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-! ## Rounding arithmetic -/

/-- The remainder of a truncating division has modulus `< b` (for `b > 0`). -/
private theorem abs_tmod_lt_x1 (A : ℤ) {b : ℤ} (hb : 0 < b) : |A.tmod b| < b := by
  rw [abs_lt]
  exact ⟨Int.lt_tmod_of_pos A hb, Int.tmod_lt_of_pos A hb⟩

/-- Rounding towards zero: `|trunc(A/b) - A/b| < 1` (as real numbers), for `b > 0`. -/
private theorem tdiv_sub_div_lt_one_x1 (A : ℤ) {b : ℤ} (hb : 0 < b) :
    |((A.tdiv b : ℤ) : ℝ) - (A : ℝ) / b| < 1 := by
  have hdec := Int.tmod_add_tdiv_mul A b
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hsplit : (A : ℝ) / b = ((A.tdiv b : ℤ) : ℝ) + ((A.tmod b : ℤ) : ℝ) / b := by
    have h : ((A.tmod b : ℤ) : ℝ) + ((A.tdiv b : ℤ) : ℝ) * (b : ℝ) = (A : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hdec
      push_cast at this
      linarith [this]
    field_simp
    linarith [h]
  have hkey : ((A.tdiv b : ℤ) : ℝ) - (A : ℝ) / b = -(((A.tmod b : ℤ) : ℝ) / b) := by
    rw [hsplit]; ring
  rw [hkey, abs_neg, abs_div, abs_of_pos hbR, div_lt_one hbR, ← Int.cast_abs]
  exact_mod_cast abs_tmod_lt_x1 A hb

/-- Truncating division never increases a coordinate: `|A.tdiv b| · |b| ≤ |A|`. -/
private theorem natAbs_tdiv_mul_le_x1 (A : ℤ) (b : ℤ) :
    (A.tdiv b).natAbs * b.natAbs ≤ A.natAbs := by
  rw [Int.natAbs_tdiv]
  exact Nat.div_mul_le_self _ _

/-- `|(2^p : ℤ)| = 2^p`. -/
private theorem natAbs_pow_two (p : ℕ) : (((2 : ℤ) ^ p).natAbs) = 2 ^ p := by
  have h1 : ((((2 : ℤ) ^ p).natAbs : ℤ)) = (2 : ℤ) ^ p := Int.natAbs_of_nonneg (by positivity)
  have h2 : (((2 ^ p : ℕ) : ℤ)) = (2 : ℤ) ^ p := by rw [Int.natCast_pow]; norm_num
  exact_mod_cast h1.trans h2.symm

private theorem two_pow_two_mul (p : ℕ) : 2 ^ (2 * p) = 4 ^ p := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]

/-! ## Complex norm bookkeeping -/

/-- Multiplying by the real scalar `2^p` inside `ℂ` and pulling it out of the norm. -/
private theorem norm_bridge (p : ℕ) (z : ℂ) :
    (2 : ℝ) ^ p * ‖z‖ = ‖((((2 : ℝ) ^ p : ℝ)) : ℂ) * z‖ := by
  rw [norm_mul]
  have h : ‖((((2 : ℝ) ^ p : ℝ)) : ℂ)‖ = (2 : ℝ) ^ p := by
    have hsq : ‖((((2 : ℝ) ^ p : ℝ)) : ℂ)‖ ^ 2 = ((2 : ℝ) ^ p) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg ((((2 : ℝ) ^ p : ℝ)) : ℂ), pow_pos (by norm_num : (0 : ℝ) < 2) p]
  rw [h]

/-- A complex number whose real and imaginary parts are `< 1` in modulus has norm `< 2`. -/
private theorem norm_lt_two_of_re_im (z : ℂ) (hr : |z.re| < 1) (hi : |z.im| < 1) : ‖z‖ < 2 := by
  have h := Complex.norm_le_abs_re_add_abs_im z
  linarith

private theorem re_add_ofReal_mul_I (a b : ℝ) : (((a : ℂ) + (b : ℂ) * Complex.I)).re = a := by
  simp [Complex.mul_re]

private theorem im_add_ofReal_mul_I (a b : ℝ) : (((a : ℂ) + (b : ℂ) * Complex.I)).im = b := by
  simp [Complex.mul_im]

/-! ## The complex algebra of the product -/

/-- `2^p · fxC p (a,b) = a + b i`. -/
private theorem fxC_smul (p : ℕ) (a b : ℤ) :
    ((((2 : ℝ) ^ p : ℝ)) : ℂ) * fxC p (a, b) = ((a : ℂ) + (b : ℂ) * Complex.I) := by
  have hM : ((((2 : ℝ) ^ p : ℝ)) : ℂ) = (2 : ℂ) ^ p := by rw [Complex.ofReal_pow]; norm_num
  have h0 : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
  rw [fxC, hM, ← mul_div_assoc]
  exact mul_div_cancel_left₀ _ h0

/-- `2^p · (fxC p u · fxC p v)` is the Gaussian product divided by `2^p`. -/
private theorem fxC_mul_smul (p : ℕ) (a b a' b' : ℤ) :
    ((((2 : ℝ) ^ p : ℝ)) : ℂ) * (fxC p (a, b) * fxC p (a', b'))
      = (((((a * a' - b * b' : ℤ)) : ℂ) + (((a * b' + b * a' : ℤ)) : ℂ) * Complex.I)
          / ((((2 : ℝ) ^ p : ℝ)) : ℂ)) := by
  have hM : ((((2 : ℝ) ^ p : ℝ)) : ℂ) = (2 : ℂ) ^ p := by rw [Complex.ofReal_pow]; norm_num
  have hprod : ((a : ℂ) + (b : ℂ) * Complex.I) * ((a' : ℂ) + (b' : ℂ) * Complex.I)
      = (((a * a' - b * b' : ℤ)) : ℂ) + (((a * b' + b * a' : ℤ)) : ℂ) * Complex.I := by
    refine Complex.ext ?_ ?_
    · simp [Complex.mul_re, Complex.mul_im]
    · simp [Complex.mul_re, Complex.mul_im]
  rw [fxC, fxC, hM]
  rw [div_mul_div_comm, ← hprod]
  field_simp

/-- Division of a Gaussian integer by a nonzero real scalar, in `re + im·i` form. -/
private theorem complex_div_real (m : ℝ) (hm : m ≠ 0) (c d : ℤ) :
    (((c : ℂ) + (d : ℂ) * Complex.I) / ((m : ℝ) : ℂ))
      = ((((c : ℝ) / m : ℝ)) : ℂ) + ((((d : ℝ) / m : ℝ)) : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.div_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  · simp [Complex.div_im, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    field_simp

/-! ## The disc is closed under the truncated product -/

/-- The disc `C̃◦` is closed under the truncated product: if `u, v` have
`u.1² + u.2² ≤ 4^p` and `v.1² + v.2² ≤ 4^p`, then the componentwise truncation by `2^p` of
their Gaussian product again satisfies that inequality. -/
private theorem inDisc_mul_tdiv_aux (p : ℕ) (u v : ℤ × ℤ) (hu : inDisc p u) (hv : inDisc p v) :
    inDisc p ((u.1 * v.1 - u.2 * v.2).tdiv ((2 : ℤ) ^ p),
      (u.1 * v.2 + u.2 * v.1).tdiv ((2 : ℤ) ^ p)) := by
  set n : ℤ := (2 : ℤ) ^ p with hn
  set c : ℤ := u.1 * v.1 - u.2 * v.2 with hc
  set d : ℤ := u.1 * v.2 + u.2 * v.1 with hd
  set X : ℤ := c.tdiv n with hX
  set Y : ℤ := d.tdiv n with hY
  have hn0 : 0 < n := by rw [hn]; positivity
  have hnN : n.natAbs = 2 ^ p := by rw [hn]; exact natAbs_pow_two p
  -- Lagrange's identity plus the disc hypotheses
  have hcz : c ^ 2 + d ^ 2 ≤ (4 : ℤ) ^ p * (4 : ℤ) ^ p := by
    have hcd : c ^ 2 + d ^ 2 = (u.1 ^ 2 + u.2 ^ 2) * (v.1 ^ 2 + v.2 ^ 2) := by rw [hc, hd]; ring
    rw [hcd]
    exact mul_le_mul hu hv (by positivity) (by positivity)
  have hcn : c.natAbs ^ 2 + d.natAbs ^ 2 ≤ 4 ^ p * 4 ^ p := by
    have hcast : (((c.natAbs ^ 2 + d.natAbs ^ 2 : ℕ)) : ℤ) ≤ (((4 ^ p * 4 ^ p : ℕ)) : ℤ) := by
      rw [Int.natCast_add, Int.natCast_pow, Int.natCast_pow, Int.natAbs_sq, Int.natAbs_sq,
        Int.natCast_mul, Int.natCast_pow]
      exact hcz
    exact_mod_cast hcast
  -- truncation shrinks each coordinate
  have hXle : X.natAbs * 2 ^ p ≤ c.natAbs := by
    have h := natAbs_tdiv_mul_le_x1 c n
    rw [← hX, hnN] at h
    exact h
  have hYle : Y.natAbs * 2 ^ p ≤ d.natAbs := by
    have h := natAbs_tdiv_mul_le_x1 d n
    rw [← hY, hnN] at h
    exact h
  have hXsq : X.natAbs ^ 2 * 4 ^ p ≤ c.natAbs ^ 2 := by
    have hnat : (X.natAbs * 2 ^ p) ^ 2 ≤ c.natAbs ^ 2 := Nat.pow_le_pow_left hXle 2
    have e : (X.natAbs * 2 ^ p) ^ 2 = X.natAbs ^ 2 * 4 ^ p := by
      rw [Nat.mul_pow, ← pow_mul, Nat.mul_comm p 2, two_pow_two_mul]
    rwa [e] at hnat
  have hYsq : Y.natAbs ^ 2 * 4 ^ p ≤ d.natAbs ^ 2 := by
    have hnat : (Y.natAbs * 2 ^ p) ^ 2 ≤ d.natAbs ^ 2 := Nat.pow_le_pow_left hYle 2
    have e : (Y.natAbs * 2 ^ p) ^ 2 = Y.natAbs ^ 2 * 4 ^ p := by
      rw [Nat.mul_pow, ← pow_mul, Nat.mul_comm p 2, two_pow_two_mul]
    rwa [e] at hnat
  have hsum : (X.natAbs ^ 2 + Y.natAbs ^ 2) * 4 ^ p ≤ 4 ^ p * 4 ^ p := by
    have h : (X.natAbs ^ 2 + Y.natAbs ^ 2) * 4 ^ p
        = X.natAbs ^ 2 * 4 ^ p + Y.natAbs ^ 2 * 4 ^ p := by ring
    rw [h]
    linarith [hXsq, hYsq, hcn]
  have hfin : X.natAbs ^ 2 + Y.natAbs ^ 2 ≤ 4 ^ p := by
    have h := hsum
    rw [mul_comm (X.natAbs ^ 2 + Y.natAbs ^ 2) (4 ^ p)] at h
    exact Nat.le_of_mul_le_mul_left h (pow_pos (by norm_num) p)
  simp only [inDisc]
  have hcast : (((X.natAbs ^ 2 + Y.natAbs ^ 2 : ℕ)) : ℤ) ≤ (((4 ^ p : ℕ)) : ℤ) := by
    exact_mod_cast hfin
  rw [Int.natCast_add, Int.natCast_pow, Int.natCast_pow, Int.natAbs_sq, Int.natAbs_sq,
    Int.natCast_pow] at hcast
  exact hcast

/-! ## The approximation bound -/

/-- The second half of `mulF_approx`, with no hypothesis on the inputs: rounding the four
components of the Gaussian product towards zero keeps the error below `2` units in the last
place. -/
theorem mulF_norm_approx (p : ℕ) (x y x' y' : ℤ) :
    (2 : ℝ) ^ p * ‖fxC p ((x * x' - y * y').tdiv ((2 : ℤ) ^ p),
        (x * y' + y * x').tdiv ((2 : ℤ) ^ p)) - fxC p (x, y) * fxC p (x', y')‖ < 2 := by
  set X : ℤ := (x * x' - y * y').tdiv ((2 : ℤ) ^ p) with hX
  set Y : ℤ := (x * y' + y * x').tdiv ((2 : ℤ) ^ p) with hY
  have hm0 : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  -- the truncation error is `< 1` per coordinate
  have hXerr : |(X : ℝ) - ((x * x' - y * y' : ℤ) : ℝ) / (2 : ℝ) ^ p| < 1 := by
    have h := tdiv_sub_div_lt_one_x1 (x * x' - y * y') (b := (2 : ℤ) ^ p) (by positivity)
    simp only [hX] at h ⊢
    simpa using h
  have hYerr : |(Y : ℝ) - ((x * y' + y * x' : ℤ) : ℝ) / (2 : ℝ) ^ p| < 1 := by
    have h := tdiv_sub_div_lt_one_x1 (x * y' + y * x') (b := (2 : ℤ) ^ p) (by positivity)
    simp only [hY] at h ⊢
    simpa using h
  -- the scaled difference, explicitly
  have hD : ((((2 : ℝ) ^ p : ℝ)) : ℂ) * (fxC p (X, Y) - fxC p (x, y) * fxC p (x', y'))
      = ((((X : ℝ) - ((x * x' - y * y' : ℤ) : ℝ) / (2 : ℝ) ^ p : ℝ)) : ℂ)
        + ((((Y : ℝ) - ((x * y' + y * x' : ℤ) : ℝ) / (2 : ℝ) ^ p : ℝ)) : ℂ) * Complex.I := by
    rw [mul_sub, fxC_smul p X Y, fxC_mul_smul p x y x' y']
    rw [complex_div_real ((2 : ℝ) ^ p) (ne_of_gt hm0) (x * x' - y * y') (x * y' + y * x')]
    refine Complex.ext ?_ ?_ <;> simp [Complex.ofReal_sub, Complex.ofReal_add] <;> ring
  rw [norm_bridge p (fxC p (X, Y) - fxC p (x, y) * fxC p (x', y')), hD]
  refine norm_lt_two_of_re_im _ ?_ ?_
  · rw [re_add_ofReal_mul_I]; exact hXerr
  · rw [im_add_ofReal_mul_I]; exact hYerr

theorem mulF_approx (p : ℕ) (x y x' y' : ℤ)
    (hu : HvdH.inDisc p (x, y)) (hv : HvdH.inDisc p (x', y')) :
    HvdH.inDisc p ((x * x' - y * y').tdiv ((2 : ℤ) ^ p), (x * y' + y * x').tdiv ((2 : ℤ) ^ p)) ∧
    (2 : ℝ) ^ p * ‖HvdH.fxC p ((x * x' - y * y').tdiv ((2 : ℤ) ^ p),
        (x * y' + y * x').tdiv ((2 : ℤ) ^ p))
      - HvdH.fxC p (x, y) * HvdH.fxC p (x', y')‖ < 2 :=
  ⟨inDisc_mul_tdiv_aux p (x, y) (x', y') hu hv, mulF_norm_approx p x y x' y'⟩

end Work.Fx
