import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs

namespace Work.ZeroFreeTables.P9

open Complex

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

/-- The exact evaluation of `Φ(x,y,t) = Re P₃(x/(y+it))` for `y > 0`. -/
private lemma phi_formula (a b c : ℝ) (hb : 0 < b) : PhiG a b c = a*Q a b c/(b^2+c^2)^3 := by
  have hD : b^2+c^2 ≠ 0 := by positivity
  unfold PhiG
  rw [P3_re, re_div a b c, im_div a b c]
  unfold Q
  field_simp
  ring

/-- The algebraic identity behind the comparison of `Φ` at two arguments:
`(8/3)a⁹(b²+c²)³ − a b³ Q(a,b,c)(a²+c²)³ = (a−b)·E(a,b,c)`. -/
private lemma D_factor (a b c : ℝ) :
    (8/3)*a^9*(b^2+c^2)^3 - a*b^3*Q a b c*(a^2+c^2)^3 = (a-b)*E a b c := by
  unfold Q E
  ring

/-- The comparison identity: `Φ(a,b,c) − (a/b)³Φ(a,a,c)` factors through
`(b−a)·E`, with a positive denominator. -/
private lemma phi_cmp (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    PhiG a b c - (a/b)^3 * PhiG a a c = (b-a)*E a b c/(b^3*(b^2+c^2)^3*(a^2+c^2)^3) := by
  have hQaa : Q a a c = (8/3)*a^5 := by unfold Q; ring
  rw [phi_formula a b c hb, phi_formula a a c ha, hQaa]
  field_simp
  unfold Q E
  ring

/-- `Φ(a,b,c) ≤ (a/b)³Φ(a,a,c)` for `0 < b ≤ a`. -/
private lemma PhiG_le_self (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (h : b ≤ a) :
    PhiG a b c ≤ (a/b)^3 * PhiG a a c := by
  have hkey := phi_cmp a b c ha hb
  have hE : 0 ≤ E a b c := E_nonneg a b c (le_of_lt ha) (le_of_lt hb)
  have hnum : (b-a)*E a b c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hE
  have hden : 0 ≤ b^3*(b^2+c^2)^3*(a^2+c^2)^3 := by positivity
  have : PhiG a b c - (a/b)^3 * PhiG a a c ≤ 0 := by
    rw [hkey]; exact div_nonpos_of_nonpos_of_nonneg hnum hden
  linarith

/-- `(a/b)³Φ(a,a,c) ≤ Φ(a,b,c)` for `0 < a ≤ b`. -/
private lemma PhiG_ge_self (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a ≤ b) :
    (a/b)^3 * PhiG a a c ≤ PhiG a b c := by
  have hkey := phi_cmp a b c ha hb
  have hE : 0 ≤ E a b c := E_nonneg a b c (le_of_lt ha) (le_of_lt hb)
  have hnum : 0 ≤ (b-a)*E a b c := mul_nonneg (by linarith) hE
  have hden : 0 ≤ b^3*(b^2+c^2)^3*(a^2+c^2)^3 := by positivity
  have : 0 ≤ PhiG a b c - (a/b)^3 * PhiG a a c := by
    rw [hkey]; exact div_nonneg hnum hden
  linarith

theorem rescale_variants :
    (∀ (a lam₁ lam₀ K t : ℝ), 0 < a → 0 ≤ lam₁ → lam₁ ≤ lam₀ → 0 < K →
        (K ^ 2 + 3 / 4) / (a + lam₁) ^ 3 + K / (a + lam₀) ^ 3 ≥ K / a ^ 3 →
        0 ≤ (K ^ 2 + 3 / 4) * Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₁) t
              + K * Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₀) t
              - K * Work.ZeroFreeTables.P9.PhiG (a + lam₁) a t) ∧
    (∀ (a lam₁ lam₀ K t : ℝ), 0 < a → 0 ≤ lam₁ → lam₁ ≤ lam₀ → 0 < K →
        K / (a + lam₁) ^ 3 + (1 / 2) / (a + lam₀) ^ 3 ≥ (1 / 4) / a ^ 3 →
        0 ≤ K * Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₁) t
              + (1 / 2) * Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₀) t
              - (1 / 4) * Work.ZeroFreeTables.P9.PhiG (a + lam₁) a t) ∧
    (∀ (a lam₁ K t : ℝ), 0 < a → 0 ≤ lam₁ → 0 < K →
        (K ^ 2 + 3 / 4) / (a + lam₁) ^ 3 ≥ K / a ^ 3 →
        0 ≤ (K ^ 2 + 3 / 4) * Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₁) t
              - K * Work.ZeroFreeTables.P9.PhiG (a + lam₁) a t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a lam₁ lam₀ K t ha hlam1 hlam10 hK hcond
    set L1 : ℝ := a + lam₁ with hL1
    set L0 : ℝ := a + lam₀ with hL0
    have hL1pos : 0 < L1 := by rw [hL1]; linarith
    have hL0pos : 0 < L0 := by rw [hL0]; linarith
    have hL1L0 : L1 ≤ L0 := by rw [hL1, hL0]; linarith
    have haL1 : a ≤ L1 := by rw [hL1]; linarith
    have hpp : 0 ≤ PhiG L1 L1 t := PhiG_nonneg hL1pos le_rfl
    have hge : (L1/L0)^3 * PhiG L1 L1 t ≤ PhiG L1 L0 t :=
      PhiG_ge_self L1 L0 t hL1pos hL0pos hL1L0
    have hle : PhiG L1 a t ≤ (L1/a)^3 * PhiG L1 L1 t := PhiG_le_self L1 a t hL1pos ha haL1
    have hc : 0 ≤ (K^2+3/4)/L1^3 + K/L0^3 - K/a^3 := by linarith
    have key : 0 ≤ (K^2+3/4)*PhiG L1 L1 t + K*PhiG L1 L0 t - K*PhiG L1 a t := by
      have hK0 : 0 ≤ K := le_of_lt hK
      have e1 : K*((L1/L0)^3*PhiG L1 L1 t) ≤ K*PhiG L1 L0 t :=
        mul_le_mul_of_nonneg_left hge hK0
      have e2 : K*PhiG L1 a t ≤ K*((L1/a)^3*PhiG L1 L1 t) :=
        mul_le_mul_of_nonneg_left hle hK0
      have hval : (K^2+3/4)*PhiG L1 L1 t + K*((L1/L0)^3*PhiG L1 L1 t)
            - K*((L1/a)^3*PhiG L1 L1 t)
          = PhiG L1 L1 t * L1^3 * ((K^2+3/4)/L1^3 + K/L0^3 - K/a^3) := by
        field_simp
      have hnn : 0 ≤ PhiG L1 L1 t * L1^3 * ((K^2+3/4)/L1^3 + K/L0^3 - K/a^3) :=
        mul_nonneg (mul_nonneg hpp (by positivity)) hc
      rw [← hval] at hnn
      linarith
    exact key
  · intro a lam₁ lam₀ K t ha hlam1 hlam10 hK hcond
    set L1 : ℝ := a + lam₁ with hL1
    set L0 : ℝ := a + lam₀ with hL0
    have hL1pos : 0 < L1 := by rw [hL1]; linarith
    have hL0pos : 0 < L0 := by rw [hL0]; linarith
    have hL1L0 : L1 ≤ L0 := by rw [hL1, hL0]; linarith
    have haL1 : a ≤ L1 := by rw [hL1]; linarith
    have hpp : 0 ≤ PhiG L1 L1 t := PhiG_nonneg hL1pos le_rfl
    have hge : (L1/L0)^3 * PhiG L1 L1 t ≤ PhiG L1 L0 t :=
      PhiG_ge_self L1 L0 t hL1pos hL0pos hL1L0
    have hle : PhiG L1 a t ≤ (L1/a)^3 * PhiG L1 L1 t := PhiG_le_self L1 a t hL1pos ha haL1
    have hc : 0 ≤ K/L1^3 + (1/2)/L0^3 - (1/4)/a^3 := by linarith
    have key : 0 ≤ K*PhiG L1 L1 t + (1/2)*PhiG L1 L0 t - (1/4)*PhiG L1 a t := by
      have e1 : (1/2)*((L1/L0)^3*PhiG L1 L1 t) ≤ (1/2)*PhiG L1 L0 t :=
        mul_le_mul_of_nonneg_left hge (by norm_num)
      have e2 : (1/4)*PhiG L1 a t ≤ (1/4)*((L1/a)^3*PhiG L1 L1 t) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
      have hval : K*PhiG L1 L1 t + (1/2)*((L1/L0)^3*PhiG L1 L1 t)
            - (1/4)*((L1/a)^3*PhiG L1 L1 t)
          = PhiG L1 L1 t * L1^3 * (K/L1^3 + (1/2)/L0^3 - (1/4)/a^3) := by
        field_simp
      have hnn : 0 ≤ PhiG L1 L1 t * L1^3 * (K/L1^3 + (1/2)/L0^3 - (1/4)/a^3) :=
        mul_nonneg (mul_nonneg hpp (by positivity)) hc
      rw [← hval] at hnn
      linarith
    exact key
  · intro a lam₁ K t ha hlam1 hK hcond
    set L1 : ℝ := a + lam₁ with hL1
    have hL1pos : 0 < L1 := by rw [hL1]; linarith
    have haL1 : a ≤ L1 := by rw [hL1]; linarith
    have hpp : 0 ≤ PhiG L1 L1 t := PhiG_nonneg hL1pos le_rfl
    have hle : PhiG L1 a t ≤ (L1/a)^3 * PhiG L1 L1 t := PhiG_le_self L1 a t hL1pos ha haL1
    have hc : 0 ≤ (K^2+3/4)/L1^3 - K/a^3 := by linarith
    have key : 0 ≤ (K^2+3/4)*PhiG L1 L1 t - K*PhiG L1 a t := by
      have hK0 : 0 ≤ K := le_of_lt hK
      have e2 : K*PhiG L1 a t ≤ K*((L1/a)^3*PhiG L1 L1 t) :=
        mul_le_mul_of_nonneg_left hle hK0
      have hval : (K^2+3/4)*PhiG L1 L1 t - K*((L1/a)^3*PhiG L1 L1 t)
          = PhiG L1 L1 t * L1^3 * ((K^2+3/4)/L1^3 - K/a^3) := by
        field_simp
      have hnn : 0 ≤ PhiG L1 L1 t * L1^3 * ((K^2+3/4)/L1^3 - K/a^3) :=
        mul_nonneg (mul_nonneg hpp (by positivity)) hc
      rw [← hval] at hnn
      linarith
    exact key

end

end Work.ZeroFreeTables.P9
