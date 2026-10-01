import Mathlib
import Submission.Work.ZeroFreeTables.P3.Defs
import Submission.Work.ZeroFreeTables.P3.P3Bounds

namespace Work.ZeroFreeTables.P3

noncomputable section

/-! ### The `φ`-comparisons of HB's `P₃`

These are the (private) helpers of `P3Bounds.lean`, re-derived here because the
rescaling argument is needed with a different coefficient triple `(2K, 1/2, 1/2)`
(that of HB (9.12)) rather than `(K²+3/4, 2K, K)`. -/

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

/-- `Re P₃(α/(β+it)) ≥ 0` for `0 < α ≤ β` (HB's condition (4.11)). -/
private lemma phi_nonneg (a b c : ℝ) (ha : 0 < a) (hab : a ≤ b) : 0 ≤ phi a b c := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [phi_formula a b c hb]
  apply div_nonneg
  · apply mul_nonneg (le_of_lt ha)
    unfold Q
    have h1 : 0 ≤ (b-a)*c^4 := mul_nonneg (by linarith) (by positivity)
    have h2 : 0 ≤ 2*b*(b^2-a^2)*c^2 := by
      apply mul_nonneg
      · apply mul_nonneg (by positivity)
        nlinarith
      · positivity
    have h3 : 0 ≤ b^3*(b^2+a*b+(2/3)*a^2) := by positivity
    linarith
  · positivity

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

/-- `(a/b)³φ(a,a,c) ≤ φ(a,b,c)` for `0 < a ≤ b`. -/
private lemma phi_ge (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a ≤ b) :
    (a/b)^3 * phi a a c ≤ phi a b c := by
  have hkey := phi_cmp a b c ha hb
  have hE : 0 ≤ E a b c := E_nonneg a b c (le_of_lt ha) (le_of_lt hb)
  have hnum : 0 ≤ (b-a)*E a b c := mul_nonneg (by linarith) hE
  have hden : 0 ≤ b^3*(b^2+c^2)^3*(a^2+c^2)^3 := by positivity
  have : 0 ≤ phi a b c - (a/b)^3 * phi a a c := by
    rw [hkey]; exact div_nonneg hnum hden
  linarith

/-! ### The rescaling argument with general coefficients -/

/-- **HB's rescaling argument**, general coefficients.

For `0 < a`, `0 ≤ λ₁ ≤ λ₀`, any `t`, any coefficients `c₀, c₁, c₂ ≥ 0` satisfying
`c₀/(a+λ₁)³ + c₁/(a+λ₀)³ ≥ c₂/a³`, one has

`0 ≤ c₀ φ(α,α,t) + c₁ φ(α,a+λ₀,t) − c₂ φ(α,a,t)`,  `α = a + λ₁`, `φ(x,y,c) = Re P₃(x/(y+ic))`.

Indeed `φ(α,α,t) ≥ 0`, `φ(α,a+λ₀,t) ≥ (α/(a+λ₀))³ φ(α,α,t)` (since `α ≤ a+λ₀`) and
`φ(α,a,t) ≤ (α/a)³ φ(α,α,t)` (since `a ≤ α`), so the expression is at least
`φ(α,α,t)·α³·(c₀/α³ + c₁/(a+λ₀)³ − c₂/a³) ≥ 0`. -/
private lemma rescale_gen (a lam₁ lam₀ t c₀ c₁ c₂ : ℝ) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    (hlam : lam₁ ≤ lam₀) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcond : c₀ / (a + lam₁) ^ 3 + c₁ / (a + lam₀) ^ 3 ≥ c₂ / a ^ 3) :
    0 ≤ c₀ * phi (a + lam₁) (a + lam₁) t + c₁ * phi (a + lam₁) (a + lam₀) t
        - c₂ * phi (a + lam₁) a t := by
  set α : ℝ := a + lam₁ with hα
  have hαpos : 0 < α := by rw [hα]; linarith
  have hL0pos : 0 < a + lam₀ := by linarith
  have hαa : a ≤ α := by rw [hα]; linarith
  have hαL0 : α ≤ a + lam₀ := by rw [hα]; linarith
  have hp : 0 ≤ phi α α t := phi_nonneg α α t hαpos le_rfl
  have hup : (α/(a+lam₀))^3 * phi α α t ≤ phi α (a+lam₀) t :=
    phi_ge α (a+lam₀) t hαpos hL0pos hαL0
  have hlow : phi α a t ≤ (α/a)^3 * phi α α t := phi_le α a t hαpos ha hαa
  have hc : 0 ≤ c₀/α^3 + c₁/(a+lam₀)^3 - c₂/a^3 := by linarith
  have e1 : c₁ * ((α/(a+lam₀))^3 * phi α α t) ≤ c₁ * phi α (a+lam₀) t :=
    mul_le_mul_of_nonneg_left hup hc₁
  have e2 : c₂ * phi α a t ≤ c₂ * ((α/a)^3 * phi α α t) :=
    mul_le_mul_of_nonneg_left hlow hc₂
  have hval : c₀ * phi α α t + c₁ * ((α/(a+lam₀))^3 * phi α α t)
        - c₂ * ((α/a)^3 * phi α α t)
      = phi α α t * α^3 * (c₀/α^3 + c₁/(a+lam₀)^3 - c₂/a^3) := by
    field_simp
  have hnn : 0 ≤ phi α α t * α^3 * (c₀/α^3 + c₁/(a+lam₀)^3 - c₂/a^3) :=
    mul_nonneg (mul_nonneg hp (by positivity)) hc
  rw [← hval] at hnn
  linarith

/-- The complex expression of `CaseC_D` written through `φ`. -/
private lemma re_combination (a lam₁ lam₀ K t : ℝ) :
    (2 * K * Work.ZeroFreeTables.P3 ((a + lam₁) / ((a + lam₁) + (t : ℂ) * Complex.I))
        + (1/2) * Work.ZeroFreeTables.P3 ((a + lam₁) / ((a + lam₀) + (t : ℂ) * Complex.I))
        - (1/2) * Work.ZeroFreeTables.P3 ((a + lam₁) / (a + (t : ℂ) * Complex.I))).re
      = 2 * K * phi (a + lam₁) (a + lam₁) t + (1/2) * phi (a + lam₁) (a + lam₀) t
        - (1/2) * phi (a + lam₁) a t := by
  simp only [phi]
  simp only [Complex.add_re, Complex.sub_re]
  simp [Complex.mul_re]

/-- HB §9, case `χ₁² = χ₀`: the `D ≥ 0` step, HB (9.12).
`D = Re{2K P₃(α/((a+λ₁)+it)) + (1/2)P₃(α/((a+λ₀)+it)) - (1/2)P₃(α/(a+it))}` with `α = a+λ₁`, and
`2K/(a+λ₁)³ + (1/2)/(a+λ₀)³ ≥ (1/2)/a³`.

Same rescaling argument as `P3Bounds`'s second conjunct with coefficients `(2K, 1/2, 1/2)`:
`D ≥ φ(α,α,t)·α³·(2K/α³ + (1/2)/(a+λ₀)³ − (1/2)/a³) ≥ 0`. -/
theorem CaseC_D {a lam₁ lam₀ K t : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hlam₁ : 0 ≤ lam₁)
    (hlam : lam₁ ≤ lam₀)
    (hcond : 2 * K / (a + lam₁) ^ 3 + (1/2) / (a + lam₀) ^ 3 ≥ (1/2) / a ^ 3) :
    0 ≤ (2 * K * Work.ZeroFreeTables.P3 ((a + lam₁) / ((a + lam₁) + (t : ℂ) * Complex.I))
        + (1/2) * Work.ZeroFreeTables.P3 ((a + lam₁) / ((a + lam₀) + (t : ℂ) * Complex.I))
        - (1/2) * Work.ZeroFreeTables.P3 ((a + lam₁) / (a + (t : ℂ) * Complex.I))).re := by
  rw [re_combination]
  exact rescale_gen a lam₁ lam₀ t (2*K) (1/2) (1/2) ha hlam₁ hlam (by positivity)
    (by norm_num) (by norm_num) hcond

end

end Work.ZeroFreeTables.P3
