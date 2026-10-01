import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.XY.SupDefs
import Submission.Work.ZeroFreeTables.XY.Tf72FcClosed

namespace Work.ZeroFreeTables.XY

/-!
# ZeroFreeTables — XY/XyReDecompB

The explicit real decomposition of `xyRe x t = Re (tf72Fc (4/3) (x + i t))` into a
"rational" (non-exponential) part `ReQ` and an `exp (-(3x/2))`-weighted trigonometric part
with coefficients `ReP`, `ImP`.  This is obtained by taking real parts in the closed form
`Tf72FcClosed` for `tf72Fc (4/3)`.

The proof is a purely algebraic computation: writing `z = x + i t`, the closed form is
`64/45/z − 512/81/z³ + 1024/81/z⁴ − 16384/729/z⁶
   + e^{−3z/2}(1024/81/z⁴ + 8192/243/z⁵ + 16384/729/z⁶)`,
and for each `k` the real and imaginary parts of `z^k` and `normSq (z^k) = (x²+t²)^k` are
evaluated; finally `e^{−3z/2} = e^{−3x/2}(cos(3t/2) − i sin(3t/2))` is separated.
-/

private lemma zpow_re_3 (x t : ℝ) : (((x:ℂ)+(t:ℂ)*Complex.I)^3).re = x^3 - 3*x*t^2 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_succ, pow_zero, Complex.one_re, Complex.one_im]
  ring

private lemma zpow_im_3 (x t : ℝ) : (((x:ℂ)+(t:ℂ)*Complex.I)^3).im = 3*x^2*t - t^3 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_succ, pow_zero, Complex.one_re, Complex.one_im]
  ring

private lemma zpow_re_4 (x t : ℝ) : (((x:ℂ)+(t:ℂ)*Complex.I)^4).re = x^4 - 6*x^2*t^2 + t^4 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_succ, pow_zero, Complex.one_re, Complex.one_im]
  ring

private lemma zpow_im_4 (x t : ℝ) : (((x:ℂ)+(t:ℂ)*Complex.I)^4).im = 4*x^3*t - 4*x*t^3 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_succ, pow_zero, Complex.one_re, Complex.one_im]
  ring

private lemma zpow_re_5 (x t : ℝ) : (((x:ℂ)+(t:ℂ)*Complex.I)^5).re = x^5 - 10*x^3*t^2 + 5*x*t^4 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_succ, pow_zero, Complex.one_re, Complex.one_im]
  ring

private lemma zpow_im_5 (x t : ℝ) : (((x:ℂ)+(t:ℂ)*Complex.I)^5).im = 5*x^4*t - 10*x^2*t^3 + t^5 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_succ, pow_zero, Complex.one_re, Complex.one_im]
  ring

private lemma zpow_re_6 (x t : ℝ) : (((x:ℂ)+(t:ℂ)*Complex.I)^6).re = x^6 - 15*x^4*t^2 + 15*x^2*t^4 - t^6 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_succ, pow_zero, Complex.one_re, Complex.one_im]
  ring

private lemma zpow_im_6 (x t : ℝ) : (((x:ℂ)+(t:ℂ)*Complex.I)^6).im = 6*x^5*t - 20*x^3*t^3 + 6*x*t^5 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_succ, pow_zero, Complex.one_re, Complex.one_im]
  ring

private lemma normSq_base (x t : ℝ) : Complex.normSq ((x:ℂ)+(t:ℂ)*Complex.I) = x^2+t^2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add]
  ring

private lemma normSq_zpow (x t : ℝ) (k : ℕ) :
    Complex.normSq (((x:ℂ)+(t:ℂ)*Complex.I)^k) = (x^2+t^2)^k := by
  rw [map_pow]
  congr 1
  exact normSq_base x t

/-- The separation of the exponential factor:
`e^{−3(x+it)/2} = e^{−3x/2} cos(3t/2) − i e^{−3x/2} sin(3t/2)`. -/
private lemma exp_split (x t : ℝ) :
    Complex.exp (-(3*((x:ℂ)+(t:ℂ)*Complex.I)/2))
      = ((Real.exp (-(3*x/2)) * Real.cos (3*t/2) : ℝ) : ℂ)
        + ((-(Real.exp (-(3*x/2)) * Real.sin (3*t/2)) : ℝ) : ℂ) * Complex.I := by
  have hw : -(3*((x:ℂ)+(t:ℂ)*Complex.I)/2)
      = ((-(3*x/2) : ℝ) : ℂ) + ((-(3*t/2) : ℝ):ℂ) * Complex.I := by
    push_cast; ring
  rw [hw, Complex.exp_add, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg (3*t/2), Real.sin_neg (3*t/2), ← Complex.ofReal_exp]
  push_cast
  ring

theorem XyReDecompB (x t : ℝ) (hxt : x^2 + t^2 ≠ 0) :
    Work.ZeroFreeTables.xyRe x t = Work.ZeroFreeTables.XY.ReQ x t
      + Real.exp (-(3*x/2)) * (Real.cos (3*t/2) * Work.ZeroFreeTables.XY.ReP x t + Real.sin (3*t/2) * Work.ZeroFreeTables.XY.ImP x t) := by
  have hz : ((x:ℂ) + (t:ℂ)*Complex.I) ≠ 0 := by
    intro h
    apply hxt
    have hre : x = 0 := by
      have := congrArg Complex.re h
      simpa using this
    have him : t = 0 := by
      have := congrArg Complex.im h
      simpa using this
    rw [hre, him]; norm_num
  rw [show Work.ZeroFreeTables.xyRe x t
        = (tf72Fc (4/3) ((x:ℂ)+(t:ℂ)*Complex.I)).re from rfl]
  rw [Tf72FcClosed _ hz]
  rw [exp_split x t]
  unfold ReQ ReP ImP
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, zpow_re_3, zpow_im_3, zpow_re_4, zpow_im_4,
    zpow_re_5, zpow_im_5, zpow_re_6, zpow_im_6, normSq_base, normSq_zpow,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  field_simp
  ring

end Work.ZeroFreeTables.XY
