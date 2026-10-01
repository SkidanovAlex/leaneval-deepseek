/-
# `Work.ZeroFreeTables.Rep9.P3_div_le` — the `P₃`-comparison (℘-comparison)

For `0 < y ≤ x` and real `t`,

  `Re P₃(x/(y+it)) ≤ (x/y)³ · Re P₃(x/(x+it))`,

HB's polynomial `P₃(X) = X + X² + (2/3)X³` of (4.12).

This is the comparison used in the order-3 (§9 diagonal) case of `Rep9`, where the
principal-character pole term `Re P₃(α/(a+iμ))` has to be dominated by `(α/a)³` times the
reference term `Re P₃(α/(α+iμ))`.  The proof is the exact algebra of
`P3/P3Bounds.lean` (whose version of it is `private`, hence re-derived here):

* `Re P₃(a/(b+ic))·(b²+c²)³ = a·Q(a,b,c)` with
  `Q = (b−a)c⁴ + 2b(b²−a²)c² + b³(b²+ab+(2/3)a²)`;
* `φ(a,b,c) − (a/b)³φ(a,a,c) = (b−a)·E(a,b,c)/(b³(b²+c²)³(a²+c²)³)`,
  where `E` is a sum of monomials in `a`, `b`, `c²` with non-negative coefficients.

Hence for `b ≤ a` the difference is `≤ 0`, which is the claim with `a = x`, `b = y`, `c = t`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P3.P3Bounds

namespace Work.ZeroFreeTables.Rep9

noncomputable section

namespace P3div

/-- `φ(a,b,c) = Re P₃(a/(b+ic))`. -/
private def phi (x y c : ℝ) : ℝ :=
  (Work.ZeroFreeTables.P3 ((x:ℂ)/((y:ℂ)+(c:ℂ)*Complex.I))).re

/-- The numerator of `Re P₃(a/(b+ic))·(b²+c²)³`:
`(b−a)c⁴ + 2b(b²−a²)c² + b³(b²+ab+(2/3)a²)`. -/
private def Q (a b c : ℝ) : ℝ :=
  (b-a)*c^4 + 2*b*(b^2-a^2)*c^2 + b^3*(b^2+a*b+(2/3)*a^2)

/-- The non-negative factor in the comparison identity for `Re P₃`; a sum of
monomials in `a`, `b` and `c²` with positive coefficients. -/
private def E (a b c : ℝ) : ℝ :=
  a*b^3*(c^2)^5 + 2*a*b^5*(c^2)^4 + a*b^7*(c^2)^3
  + 2*a^2*b^4*(c^2)^4 + 2*a^2*b^6*(c^2)^3
  + 3*a^3*b^3*(c^2)^4 + (26/3)*a^3*b^5*(c^2)^3 + 3*a^3*b^7*(c^2)^2
  + (26/3)*a^4*b^4*(c^2)^3 + 6*a^4*b^6*(c^2)^2
  + (17/3)*a^5*b^3*(c^2)^3 + 14*a^5*b^5*(c^2)^2 + 3*a^5*b^7*(c^2)
  + (8/3)*a^6*b^2*(c^2)^3 + 14*a^6*b^4*(c^2)^2 + 6*a^6*b^6*(c^2)
  + (8/3)*a^7*b*(c^2)^3 + 9*a^7*b^3*(c^2)^2 + 10*a^7*b^5*(c^2) + a^7*b^7
  + (8/3)*a^8*(c^2)^3 + 8*a^8*b^2*(c^2)^2 + 10*a^8*b^4*(c^2) + 2*a^8*b^6

/-- `E` is non-negative in the region of interest. -/
private lemma E_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ E a b c := by
  unfold E
  positivity

/-- The real part of `P₃` at `w = x + iy` in terms of `x` and `y`. -/
private lemma P3_re (w : ℂ) :
    (Work.ZeroFreeTables.P3 w).re = w.re + (w.re^2 - w.im^2) + (2/3)*(w.re^3 - 3*w.re*w.im^2) := by
  have h23 : (2/3 : ℂ) = ((2/3 : ℝ) : ℂ) := by norm_num
  simp only [Work.ZeroFreeTables.P3, h23]
  rw [show w^2 = w*w by ring, show w^3 = w*w*w by ring]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Real part of `a/(b+ic)`. -/
private lemma re_div (a b c : ℝ) :
    (((a:ℂ)/((b:ℂ)+(c:ℂ)*Complex.I)).re) = a*b/(b^2+c^2) := by
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

/-- Imaginary part of `a/(b+ic)`. -/
private lemma im_div (a b c : ℝ) :
    (((a:ℂ)/((b:ℂ)+(c:ℂ)*Complex.I)).im) = -(a*c)/(b^2+c^2) := by
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

/-- The exact evaluation of `Re P₃(a/(b+ic))` for `b > 0`. -/
private lemma phi_formula (a b c : ℝ) (hb : 0 < b) : phi a b c = a*Q a b c/(b^2+c^2)^3 := by
  have hD : b^2+c^2 ≠ 0 := by positivity
  simp only [phi]
  rw [P3_re, re_div a b c, im_div a b c]
  unfold Q
  field_simp
  ring

/-- The comparison identity: `φ(a,b,c) − (a/b)³φ(a,a,c)` factors through
`(b−a)·E`, with a positive denominator. -/
private lemma phi_cmp (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    phi a b c - (a/b)^3 * phi a a c = (b-a)*E a b c/(b^3*(b^2+c^2)^3*(a^2+c^2)^3) := by
  have hQaa : Q a a c = (8/3)*a^5 := by unfold Q; ring
  rw [phi_formula a b c hb, phi_formula a a c ha, hQaa]
  field_simp
  unfold Q E
  ring

/-- `φ(a,b,c) ≤ (a/b)³φ(a,a,c)` for `0 < b ≤ a`. -/
private lemma phi_le (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (h : b ≤ a) :
    phi a b c ≤ (a/b)^3 * phi a a c := by
  have hkey := phi_cmp a b c ha hb
  have hE : 0 ≤ E a b c := E_nonneg a b c (le_of_lt ha) (le_of_lt hb)
  have hnum : (b-a)*E a b c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hE
  have hden : 0 ≤ b^3*(b^2+c^2)^3*(a^2+c^2)^3 := by positivity
  have : phi a b c - (a/b)^3 * phi a a c ≤ 0 := by
    rw [hkey]; exact div_nonpos_of_nonpos_of_nonneg hnum hden
  linarith

end P3div

open P3div in
theorem P3_div_le {x y t : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    (Work.ZeroFreeTables.P3 (((x : ℂ)) / (((y : ℂ)) + ((t : ℂ)) * Complex.I))).re
      ≤ (x/y)^3 * (Work.ZeroFreeTables.P3 (((x : ℂ)) / (((x : ℂ)) + ((t : ℂ)) * Complex.I))).re := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  exact phi_le x y t hx hy hyx

end

end Work.ZeroFreeTables.Rep9
