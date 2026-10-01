/-
# ZeroFreeTables — XyReDecomp

The explicit real decomposition of `Re (tf72Fc (4/3) (x + it))`, i.e. of the
Laplace transform of the test function of HB (1992) Lemma 7.2 with `λ = 4/3`,
separated into its "rational" part `ReQ` and the `exp (-(3x/2))`-weighted
trigonometric part with coefficients `ReP` and `ImP` (see `SupDefs`).

The starting point is the closed form `Tf72FcClosed` for `tf72Fc (4/3)`:

  `tf72Fc (4/3) z = (64/45)/z - (512/81)/z³ + (1024/81)/z⁴ - (16384/729)/z⁶
      + e^{-3z/2} ( (1024/81)/z⁴ + (8192/243)/z⁵ + (16384/729)/z⁶ )`   (`z ≠ 0`).

Writing `z = x + it`, so that `z⁻¹ = conj z / (x²+t²)` with
`x² + t² = normSq z ≠ 0`, and using

  `e^{-3z/2} = e^{-3x/2} (cos (3t/2) - i sin (3t/2))`,

the real part of each term of the closed form is computed by `XyInvPowReIm`:
`Re (z^{-k})` (and `Im (z^{-k})`) are exactly the rational functions appearing in
`ReQ`, `ReP` and `ImP`.  The final identity is then a ring identity in `x` and `t`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.XY.SupDefs
import Submission.Work.ZeroFreeTables.XY.Tf72FcClosed
import Submission.Work.ZeroFreeTables.XY.XyInvPowReIm
import Submission.Work.ZeroFreeTables.testFn72_defs

open Complex

noncomputable section

namespace Work.ZeroFreeTables.XY

/-! ## Real/imaginary parts of the elementary factors -/

lemma re_ofReal_mul (c : ℝ) (w : ℂ) : (((c : ℝ) : ℂ) * w).re = c * w.re := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring

lemma im_ofReal_mul (c : ℝ) (w : ℂ) : (((c : ℝ) : ℂ) * w).im = c * w.im := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

/-- Real part of the product of `c - s i` (`c, s` real) with an arbitrary complex
number: the elementary identity behind the `exp (-3z/2)` factor. -/
lemma re_sub_mul_I_mul (c s : ℝ) (w : ℂ) :
    ((((c : ℝ) : ℂ) - ((s : ℝ) : ℂ) * Complex.I) * w).re = c * w.re + s * w.im := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- `exp (-3(x+it)/2) = exp (-3x/2) (cos (3t/2) - i sin (3t/2))`. -/
lemma exp_neg_three_halves (x t : ℝ) :
    Complex.exp (-(3 * ((x : ℂ) + (t : ℂ) * Complex.I) / 2))
      = ((Real.exp (-(3 * x / 2)) : ℝ) : ℂ) *
        (((Real.cos (3 * t / 2) : ℝ) : ℂ)
          - ((Real.sin (3 * t / 2) : ℝ) : ℂ) * Complex.I) := by
  have h : (-(3 * ((x : ℂ) + (t : ℂ) * Complex.I) / 2))
      = (((-(3 * x / 2) : ℝ)) : ℂ) + (((-(3 * t / 2) : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

/-! ## The main decomposition -/

theorem XyReDecomp (x t : ℝ) (hxt : x^2 + t^2 ≠ 0) :
    xyRe x t = ReQ x t
      + Real.exp (-(3*x/2)) * (Real.cos (3*t/2) * ReP x t + Real.sin (3*t/2) * ImP x t) := by
  -- `z = x + it ≠ 0`
  have hz : ((x : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    apply hxt
    have h1 : x = 0 := by
      have := congrArg Complex.re h; simpa using this
    have h2 : t = 0 := by
      have := congrArg Complex.im h; simpa using this
    rw [h1, h2]; norm_num
  -- the closed form of `Tf72FcClosed`, in the `(z^k)⁻¹` shape used below
  have hclosed : tf72Fc (4/3) ((x : ℂ) + (t : ℂ) * Complex.I)
      = ((64/45 : ℝ) : ℂ) * (((x : ℂ) + (t : ℂ) * Complex.I))⁻¹
        - ((512/81 : ℝ) : ℂ) * ((((x : ℂ) + (t : ℂ) * Complex.I)^3)⁻¹)
        + ((1024/81 : ℝ) : ℂ) * ((((x : ℂ) + (t : ℂ) * Complex.I)^4)⁻¹)
        - ((16384/729 : ℝ) : ℂ) * ((((x : ℂ) + (t : ℂ) * Complex.I)^6)⁻¹)
        + Complex.exp (-(3 * ((x : ℂ) + (t : ℂ) * Complex.I) / 2)) *
          (((1024/81 : ℝ) : ℂ) * ((((x : ℂ) + (t : ℂ) * Complex.I)^4)⁻¹)
            + ((8192/243 : ℝ) : ℂ) * ((((x : ℂ) + (t : ℂ) * Complex.I)^5)⁻¹)
            + ((16384/729 : ℝ) : ℂ) * ((((x : ℂ) + (t : ℂ) * Complex.I)^6)⁻¹)) := by
    rw [Tf72FcClosed _ hz]
    push_cast
    ring
  show (tf72Fc (4/3) ((x : ℂ) + (t : ℂ) * Complex.I)).re
      = ReQ x t
        + Real.exp (-(3*x/2)) * (Real.cos (3*t/2) * ReP x t + Real.sin (3*t/2) * ImP x t)
  rw [hclosed, ReQ, ReP, ImP]
  obtain ⟨h1, h3, h4r, h4i, h5r, h5i, h6r, h6i⟩ := XyInvPowReIm x t hxt
  rw [exp_neg_three_halves x t]
  simp only [Complex.add_re, Complex.sub_re]
  simp only [re_ofReal_mul]
  rw [mul_assoc, re_ofReal_mul, re_sub_mul_I_mul]
  simp only [Complex.add_re, re_ofReal_mul, Complex.add_im, im_ofReal_mul]
  rw [h1, h3, h4r, h4i, h5r, h5i, h6r, h6i]

end Work.ZeroFreeTables.XY
