/-
# ZeroFreeTables/P3/P3Bounds — the two elementary bounds on HB's `P₃`

The definitional part of Heath-Brown's §9 inequality (9.13): the pointwise
non-negativity of `Re P₃` on the strip `0 < α ≤ β`,

  `Re P₃(α/(β+it)) ≥ 0`  (`0 < α ≤ β`),

and the purely algebraic step (9.9)–(9.12), namely that the combination

  `A913 a λ₁ λ₀ K Δ = Re{(K²+3/4)P₃((a+λ₁)/((a+λ₁)+iΔ)) + 2K P₃((a+λ₁)/((a+λ₀)+iΔ))
                            − K P₃((a+λ₁)/(a+iΔ))}`

is non-negative as soon as the side condition
`(K²+3/4)/(a+λ₁)³ + 2K/(a+λ₀)³ ≥ K/a³` holds.

Both rest on the exact evaluation, for real `a`, `b` and `c` with `b > 0`,

  `Re P₃(a/(b+ic)) · (b²+c²)³
     = a·[(b−a)c⁴ + 2b(b²−a²)c² + b³(b²+ab+(2/3)a²)]`,

from which `Re P₃(a/(b+ic)) (b²+c²)³ ≥ 0` whenever `0 < a ≤ b` (each of the three
terms is non-negative).  The comparison of `Re P₃(a/(b+ic))` with `(a/b)³ Re P₃(a/(a+ic))`
is the identity

  `Re P₃(a/(b+ic)) − (a/b)³ Re P₃(a/(a+ic))
      = (b−a)·E a b c / (b³ (b²+c²)³ (a²+c²)³)`

with `E ≥ 0` a sum of monomials in `a`, `b`, `c²` with non-negative coefficients;
this is where the side condition is consumed.  Note that `P₃` here is HB's third
polynomial `P₃(X) = X + X² + (2/3)X³` of (4.12).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.Defs

namespace Work.ZeroFreeTables.P3

noncomputable section

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

/-- `φ(a,b,c) = Re P₃(a/(b+ic))`. -/
private def phi (x y c : ℝ) : ℝ :=
  (Work.ZeroFreeTables.P3 ((x:ℂ)/((y:ℂ)+(c:ℂ)*Complex.I))).re

/-- The algebraic identity behind the comparison of `φ` at two arguments:
`(8/3)a⁹(b²+c²)³ − a b³ Q(a,b,c)(a²+c²)³ = (a−b)·E(a,b,c)`. -/
private lemma D_factor (a b c : ℝ) :
    (8/3)*a^9*(b^2+c^2)^3 - a*b^3*Q a b c*(a^2+c^2)^3 = (a-b)*E a b c := by
  unfold Q E
  ring

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

/-- `A913` written in terms of `φ`. -/
private lemma A913_eq (a lam₁ lam₀ K Δ : ℝ) :
    Work.ZeroFreeTables.A913 a lam₁ lam₀ K Δ =
      (K^2+3/4)*phi (a+lam₁) (a+lam₁) Δ + 2*K*phi (a+lam₁) (a+lam₀) Δ
        - K*phi (a+lam₁) a Δ := by
  have h1 : (↑K : ℂ)^2 + (3/4 : ℂ) = (((K^2 + 3/4 : ℝ)) : ℂ) := by push_cast; ring
  have h2 : (2 : ℂ) * (↑K : ℂ) = (((2*K : ℝ)) : ℂ) := by push_cast; ring
  have ha1 : ((↑a : ℂ) + ↑lam₁) = (↑(a+lam₁) : ℂ) := by push_cast; ring
  have ha0 : ((↑a : ℂ) + ↑lam₀) = (↑(a+lam₀) : ℂ) := by push_cast; ring
  simp only [Work.ZeroFreeTables.A913, phi, h1, h2, ha1, ha0]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem P3Bounds :
    (∀ α β t : ℝ, 0 < α → α ≤ β →
      0 ≤ (Work.ZeroFreeTables.P3 ((α : ℂ) / ((β : ℂ) + (t : ℂ) * Complex.I))).re) ∧
    (∀ a lam₁ lam₀ K Δ : ℝ, 0 < a → 0 < K → 0 ≤ lam₁ → lam₁ ≤ lam₀ →
      (K ^ 2 + 3/4) / (a + lam₁) ^ 3 + 2 * K / (a + lam₀) ^ 3 ≥ K / a ^ 3 →
      0 ≤ Work.ZeroFreeTables.A913 a lam₁ lam₀ K Δ) := by
  constructor
  · intro α β t hα hαβ
    exact phi_nonneg α β t hα hαβ
  · intro a lam₁ lam₀ K Δ ha hK hlam₁ hlam hcond
    -- write `L1 = a + λ₁`, `L0 = a + λ₀`; then `0 < a ≤ L1 ≤ L0`.
    set L1 : ℝ := a + lam₁ with hL1
    set L0 : ℝ := a + lam₀ with hL0
    have hL1pos : 0 < L1 := by rw [hL1]; linarith
    have hL0pos : 0 < L0 := by rw [hL0]; linarith
    have h1L0 : L1 ≤ L0 := by rw [hL1, hL0]; linarith
    have haL1 : a ≤ L1 := by rw [hL1]; linarith
    -- the three pointwise informations about `φ(L1, ·, Δ)`
    have hp : 0 ≤ phi L1 L1 Δ := phi_nonneg L1 L1 Δ hL1pos le_rfl
    have hlow : phi L1 a Δ ≤ (L1/a)^3 * phi L1 L1 Δ := phi_le L1 a Δ hL1pos ha haL1
    have hup : (L1/L0)^3 * phi L1 L1 Δ ≤ phi L1 L0 Δ := phi_ge L1 L0 Δ hL1pos hL0pos h1L0
    -- the side condition, in the form in which it is consumed
    have hc : 0 ≤ (K^2+3/4)/L1^3 + 2*K/L0^3 - K/a^3 := by linarith
    have key : 0 ≤ (K^2+3/4)*phi L1 L1 Δ + 2*K*phi L1 L0 Δ - K*phi L1 a Δ := by
      have hK0 : 0 ≤ K := le_of_lt hK
      have e1 : 2*K*((L1/L0)^3 * phi L1 L1 Δ) ≤ 2*K*phi L1 L0 Δ :=
        mul_le_mul_of_nonneg_left hup (by positivity)
      have e2 : K*phi L1 a Δ ≤ K*((L1/a)^3 * phi L1 L1 Δ) :=
        mul_le_mul_of_nonneg_left hlow hK0
      have hval : (K^2+3/4)*phi L1 L1 Δ + 2*K*((L1/L0)^3*phi L1 L1 Δ)
            - K*((L1/a)^3*phi L1 L1 Δ)
          = phi L1 L1 Δ * L1^3 * ((K^2+3/4)/L1^3 + 2*K/L0^3 - K/a^3) := by
        field_simp
      have hnn : 0 ≤ phi L1 L1 Δ * L1^3 * ((K^2+3/4)/L1^3 + 2*K/L0^3 - K/a^3) :=
        mul_nonneg (mul_nonneg hp (by positivity)) hc
      rw [← hval] at hnn
      linarith
    rw [A913_eq a lam₁ lam₀ K Δ, ← hL1, ← hL0]
    exact key

end

end Work.ZeroFreeTables.P3
