import Mathlib
import Submission.Work.KMTPlan.A6.coeff2_dp_id
import Submission.Work.KMTPlan.A6.wt_tsum_le
import Submission.Work.KMTPlan.A6.coeff2_ofReal_norm_le_lintegral
import Submission.Work.KMTPlan.A6.continuous_dp

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The frequency factor `r ^ (1 - j) / (2π|p|) ^ j` attached to the `j`-th derivative bound. -/
def rho (r : ℝ) (j : ℕ) (p : ℤ) : ℝ :=
  r ^ ((1 : ℝ) - (j : ℝ)) / (2 * Real.pi * |(p : ℝ)|) ^ j

/-- The weight of the frequency `p` at scale `r`: `min r (r⁻¹/(2πp)²)`, with value `r` at `p = 0`. -/
def wt (r : ℝ) (p : ℤ) : ℝ :=
  if p = 0 then r else min r (r⁻¹ / (2 * Real.pi * |(p : ℝ)|) ^ 2)

lemma rho_zero (r : ℝ) (p : ℤ) : rho r 0 p = r := by
  simp [rho, Real.rpow_one]

lemma rho_two (r : ℝ) (p : ℤ) : rho r 2 p = r⁻¹ / (2 * Real.pi * |(p : ℝ)|) ^ 2 := by
  rw [rho, show (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]

lemma wt_zero (r : ℝ) : wt r 0 = r := by simp [wt]

lemma wt_nonneg {r : ℝ} (hr : 0 ≤ r) (p : ℤ) : 0 ≤ wt r p := by
  rw [wt]
  split_ifs with h
  · exact hr
  · exact le_min hr (div_nonneg (inv_nonneg.mpr hr) (sq_nonneg _))

lemma wt_eq_min {r : ℝ} {p : ℤ} (hp : p ≠ 0) : wt r p = min (rho r 0 p) (rho r 2 p) := by
  rw [wt, if_neg hp, rho_zero, rho_two]

lemma norm_two_pi_I (p : ℤ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * (p : ℂ))‖ = 2 * Real.pi * |(p : ℝ)| := by
  have h2 : ‖(2 : ℂ)‖ = 2 := Complex.norm_two
  have hp : ‖(p : ℂ)‖ = |(p : ℝ)| := Complex.norm_intCast p
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := Complex.norm_of_nonneg Real.pi_pos.le
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ))
        = ((2 : ℂ) * (Real.pi : ℂ)) * (Complex.I * (p : ℂ)) by ring,
      norm_mul, norm_mul, norm_mul, h2, hp, hpi, hI] <;> ring

lemma norm_two_pi_I_pow (j : ℕ) (p : ℤ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * (p : ℂ)) ^ j‖ = (2 * Real.pi * |(p : ℝ)|) ^ j := by
  rw [norm_pow, norm_two_pi_I]

lemma le_mul_min {c A x a b : ℝ} (h1 : c ≤ A * x * a) (h2 : c ≤ A * x * b) :
    c ≤ A * x * min a b := by
  rcases le_total a b with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

lemma le_min_mul {c A x a b : ℝ} (h1 : c ≤ A * a * x) (h2 : c ≤ A * b * x) :
    c ≤ A * min a b * x := by
  rcases le_total a b with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

lemma le_mul_min_min {c A x0 x2 y0 y2 : ℝ}
    (h00 : c ≤ A * x0 * y0) (h02 : c ≤ A * x0 * y2)
    (h20 : c ≤ A * x2 * y0) (h22 : c ≤ A * x2 * y2) :
    c ≤ A * min x0 x2 * min y0 y2 := by
  rcases le_total x0 x2 with hx | hx
  · rw [min_eq_left hx]
    rcases le_total y0 y2 with hy | hy
    · rw [min_eq_left hy]; exact h00
    · rw [min_eq_right hy]; exact h02
  · rw [min_eq_right hx]
    rcases le_total y0 y2 with hy | hy
    · rw [min_eq_left hy]; exact h20
    · rw [min_eq_right hy]; exact h22

variable (σ : ℝ → ℝ → ℂ)
  (hper1 : ∀ x y, σ (x + 1) y = σ x y) (hper2 : ∀ x y, σ x (y + 1) = σ x y)
  (hsm : ContDiff ℝ 4 (fun p : ℝ × ℝ => σ p.1 p.2))
  (r₁ r₂ A : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hA : 0 ≤ A)
  (hder : ∀ j₁ j₂ : ℕ, j₁ ≤ 2 → j₂ ≤ 2 →
      (∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal ‖Work.KMTPlan.A6.dp j₁ j₂ σ x y‖)
        ≤ ENNReal.ofReal (A * r₁ ^ ((1 : ℝ) - (j₁ : ℝ)) * r₂ ^ ((1 : ℝ) - (j₂ : ℝ))))

include σ hper1 hper2 hsm hr₁ hr₂ hA hder

/-- The `(j₁,j₂)`-th mixed partial has bounded Fourier coefficients. -/
lemma coeff2_dp_le {j₁ j₂ : ℕ} (h₁ : j₁ ≤ 2) (h₂ : j₂ ≤ 2) (p₁ p₂ : ℤ) :
    ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.dp j₁ j₂ σ) p₁ p₂‖
      ≤ A * r₁ ^ ((1 : ℝ) - (j₁ : ℝ)) * r₂ ^ ((1 : ℝ) - (j₂ : ℝ)) := by
  have h1 : ENNReal.ofReal ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.dp j₁ j₂ σ) p₁ p₂‖
      ≤ ∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal ‖Work.KMTPlan.A6.dp j₁ j₂ σ x y‖ :=
    coeff2_ofReal_norm_le_lintegral (Work.KMTPlan.A6.dp j₁ j₂ σ) (continuous_dp σ hsm h₁ h₂) p₁ p₂
  have h3 := le_trans h1 (hder j₁ j₂ h₁ h₂)
  have hnn : 0 ≤ A * r₁ ^ ((1 : ℝ) - (j₁ : ℝ)) * r₂ ^ ((1 : ℝ) - (j₂ : ℝ)) :=
    mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hr₁.le _)) (Real.rpow_nonneg hr₂.le _)
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h3

/-- Integration by parts in each variable turns the `(j₁,j₂)`-th derivative coefficient into
`(2πip₁)^{j₁}(2πip₂)^{j₂}` times the coefficient of `σ`, giving the frequency weight. -/
lemma coeff2_case (p₁ p₂ : ℤ) {j₁ j₂ : ℕ} (hj₁ : j₁ = 0 ∨ j₁ = 2) (hj₂ : j₂ = 0 ∨ j₂ = 2)
    (hp₁ : j₁ = 0 ∨ p₁ ≠ 0) (hp₂ : j₂ = 0 ∨ p₂ ≠ 0) :
    ‖Work.KMTPlan.A6.coeff2 σ p₁ p₂‖ ≤ A * rho r₁ j₁ p₁ * rho r₂ j₂ p₂ := by
  have hj₁2 : j₁ ≤ 2 := by rcases hj₁ with h | h <;> omega
  have hj₂2 : j₂ ≤ 2 := by rcases hj₂ with h | h <;> omega
  have hd := coeff2_dp_le σ hper1 hper2 hsm r₁ r₂ A hr₁ hr₂ hA hder hj₁2 hj₂2 p₁ p₂
  have hid := coeff2_dp_id σ hper1 hper2 hsm hj₁2 hj₂2 p₁ p₂
  have hnorm : ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.dp j₁ j₂ σ) p₁ p₂‖
      = (2 * Real.pi * |(p₁ : ℝ)|) ^ j₁ * (2 * Real.pi * |(p₂ : ℝ)|) ^ j₂
        * ‖Work.KMTPlan.A6.coeff2 σ p₁ p₂‖ := by
    rw [hid, norm_mul, norm_mul, norm_two_pi_I_pow, norm_two_pi_I_pow] <;> ring
  have hkey : (2 * Real.pi * |(p₁ : ℝ)|) ^ j₁ * (2 * Real.pi * |(p₂ : ℝ)|) ^ j₂
        * ‖Work.KMTPlan.A6.coeff2 σ p₁ p₂‖
      ≤ A * r₁ ^ ((1 : ℝ) - (j₁ : ℝ)) * r₂ ^ ((1 : ℝ) - (j₂ : ℝ)) := by
    exact hnorm ▸ hd
  have e1 : r₁ ^ ((1 : ℝ) - ((2 : ℕ) : ℝ)) = r₁⁻¹ := by
    rw [show (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have e1' : r₁ ^ ((1 : ℝ) - ((0 : ℕ) : ℝ)) = r₁ := by
    rw [show (1 : ℝ) - ((0 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have e2 : r₂ ^ ((1 : ℝ) - ((2 : ℕ) : ℝ)) = r₂⁻¹ := by
    rw [show (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have e2' : r₂ ^ ((1 : ℝ) - ((0 : ℕ) : ℝ)) = r₂ := by
    rw [show (1 : ℝ) - ((0 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  rcases hj₁ with rfl | rfl <;> rcases hj₂ with rfl | rfl
  · -- (0,0)
    rw [rho_zero, rho_zero]
    simpa only [pow_zero, mul_one, one_mul, e1', e2'] using hkey
  · -- (0,2)
    have hp₂' : p₂ ≠ 0 := hp₂.resolve_left (by norm_num : ¬ ((2 : ℕ) = 0))
    rw [rho_zero, rho_two]
    rw [e1', e2] at hkey
    simp only [pow_zero, mul_one, one_mul] at hkey
    have hpos : 0 < (2 * Real.pi * |(p₂ : ℝ)|) ^ 2 := by
      have h0 : 0 < 2 * Real.pi * |(p₂ : ℝ)| :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (by exact_mod_cast hp₂'))
      exact pow_pos h0 2
    have hdiv : ‖Work.KMTPlan.A6.coeff2 σ p₁ p₂‖
        ≤ (A * r₁ * r₂⁻¹) / (2 * Real.pi * |(p₂ : ℝ)|) ^ 2 :=
      (le_div_iff₀ hpos).mpr (by rw [mul_comm]; exact hkey)
    exact hdiv.trans (le_of_eq (by ring))
  · -- (2,0)
    have hp₁' : p₁ ≠ 0 := hp₁.resolve_left (by norm_num : ¬ ((2 : ℕ) = 0))
    rw [rho_two, rho_zero]
    rw [e1, e2'] at hkey
    simp only [pow_zero, mul_one, one_mul] at hkey
    have hpos : 0 < (2 * Real.pi * |(p₁ : ℝ)|) ^ 2 := by
      have h0 : 0 < 2 * Real.pi * |(p₁ : ℝ)| :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (by exact_mod_cast hp₁'))
      exact pow_pos h0 2
    have hdiv : ‖Work.KMTPlan.A6.coeff2 σ p₁ p₂‖
        ≤ (A * r₁⁻¹ * r₂) / (2 * Real.pi * |(p₁ : ℝ)|) ^ 2 :=
      (le_div_iff₀ hpos).mpr (by rw [mul_comm]; exact hkey)
    exact hdiv.trans (le_of_eq (by ring))
  · -- (2,2)
    have hp₁' : p₁ ≠ 0 := hp₁.resolve_left (by norm_num : ¬ ((2 : ℕ) = 0))
    have hp₂' : p₂ ≠ 0 := hp₂.resolve_left (by norm_num : ¬ ((2 : ℕ) = 0))
    rw [rho_two, rho_two]
    rw [e1, e2] at hkey
    have hpos : 0 < (2 * Real.pi * |(p₁ : ℝ)|) ^ 2 * (2 * Real.pi * |(p₂ : ℝ)|) ^ 2 := by
      have h0 : 0 < 2 * Real.pi * |(p₁ : ℝ)| :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (by exact_mod_cast hp₁'))
      have h1 : 0 < 2 * Real.pi * |(p₂ : ℝ)| :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (by exact_mod_cast hp₂'))
      exact mul_pos (pow_pos h0 2) (pow_pos h1 2)
    have hkey' : ‖Work.KMTPlan.A6.coeff2 σ p₁ p₂‖
        * ((2 * Real.pi * |(p₁ : ℝ)|) ^ 2 * (2 * Real.pi * |(p₂ : ℝ)|) ^ 2)
        ≤ A * r₁⁻¹ * r₂⁻¹ := by
      rw [mul_comm]; exact hkey
    have hdiv : ‖Work.KMTPlan.A6.coeff2 σ p₁ p₂‖
        ≤ (A * r₁⁻¹ * r₂⁻¹)
          / ((2 * Real.pi * |(p₁ : ℝ)|) ^ 2 * (2 * Real.pi * |(p₂ : ℝ)|) ^ 2) :=
      (le_div_iff₀ hpos).mpr hkey'
    exact hdiv.trans (le_of_eq (by ring))

/-- Pointwise bound for the Fourier coefficients of `σ` by `A` times the product of the two
frequency weights. -/
lemma coeff2_le (p₁ p₂ : ℤ) :
    ‖Work.KMTPlan.A6.coeff2 σ p₁ p₂‖ ≤ A * (wt r₁ p₁ * wt r₂ p₂) := by
  have h00 := coeff2_case σ hper1 hper2 hsm r₁ r₂ A hr₁ hr₂ hA hder p₁ p₂
    (j₁ := 0) (j₂ := 0) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  by_cases hp₁ : p₁ = 0
  · by_cases hp₂ : p₂ = 0
    · subst hp₁; subst hp₂
      simpa only [wt_zero, rho_zero, mul_assoc] using h00
    · subst hp₁
      have h02 := coeff2_case σ hper1 hper2 hsm r₁ r₂ A hr₁ hr₂ hA hder 0 p₂
        (j₁ := 0) (j₂ := 2) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr hp₂)
      have h := le_mul_min h00 h02
      simpa only [wt_zero, wt_eq_min hp₂, rho_zero, mul_assoc] using h
  · by_cases hp₂ : p₂ = 0
    · subst hp₂
      have h20 := coeff2_case σ hper1 hper2 hsm r₁ r₂ A hr₁ hr₂ hA hder p₁ 0
        (j₁ := 2) (j₂ := 0) (Or.inr rfl) (Or.inl rfl) (Or.inr hp₁) (Or.inl rfl)
      have h := le_min_mul h00 h20
      simpa only [wt_zero, wt_eq_min hp₁, rho_zero, mul_assoc] using h
    · have h02 := coeff2_case σ hper1 hper2 hsm r₁ r₂ A hr₁ hr₂ hA hder p₁ p₂
        (j₁ := 0) (j₂ := 2) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr hp₂)
      have h20 := coeff2_case σ hper1 hper2 hsm r₁ r₂ A hr₁ hr₂ hA hder p₁ p₂
        (j₁ := 2) (j₂ := 0) (Or.inr rfl) (Or.inl rfl) (Or.inr hp₁) (Or.inl rfl)
      have h22 := coeff2_case σ hper1 hper2 hsm r₁ r₂ A hr₁ hr₂ hA hder p₁ p₂
        (j₁ := 2) (j₂ := 2) (Or.inr rfl) (Or.inr rfl) (Or.inr hp₁) (Or.inr hp₂)
      have h := le_mul_min_min h00 h02 h20 h22
      simpa only [wt_eq_min hp₁, wt_eq_min hp₂, mul_assoc] using h

end

theorem SymToolbox_tsum_coeff2_le (σ : ℝ → ℝ → ℂ)
    (hper1 : ∀ x y, σ (x + 1) y = σ x y) (hper2 : ∀ x y, σ x (y + 1) = σ x y)
    (hsm : ContDiff ℝ 4 (fun p : ℝ × ℝ => σ p.1 p.2))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁1 : r₁ ≤ 1) (hr₂ : 0 < r₂) (hr₂1 : r₂ ≤ 1)
    {A : ℝ} (hA : 0 ≤ A)
    (hder : ∀ j₁ j₂ : ℕ, j₁ ≤ 2 → j₂ ≤ 2 →
      (∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal ‖Work.KMTPlan.A6.dp j₁ j₂ σ x y‖)
        ≤ ENNReal.ofReal (A * r₁ ^ ((1 : ℝ) - (j₁ : ℝ)) * r₂ ^ ((1 : ℝ) - (j₂ : ℝ))))
    : Summable (fun p : ℤ × ℤ => ‖Work.KMTPlan.A6.coeff2 σ p.1 p.2‖)
      ∧ (∑' p : ℤ × ℤ, ‖Work.KMTPlan.A6.coeff2 σ p.1 p.2‖) ≤ 40 * A := by
  obtain ⟨hs₁, hb₁⟩ := wt_tsum_le r₁ hr₁ hr₁1
  obtain ⟨hs₂, hb₂⟩ := wt_tsum_le r₂ hr₂ hr₂1
  have hsum₁ : Summable (fun p : ℤ => wt r₁ p) := hs₁
  have hsum₂ : Summable (fun p : ℤ => wt r₂ p) := hs₂
  have h4₁ : (∑' p : ℤ, wt r₁ p) ≤ 4 := hb₁
  have h4₂ : (∑' p : ℤ, wt r₂ p) ≤ 4 := hb₂
  have hmul : Summable (fun p : ℤ × ℤ => wt r₁ p.1 * wt r₂ p.2) :=
    hsum₁.mul_of_nonneg hsum₂ (fun p => wt_nonneg hr₁.le p) (fun p => wt_nonneg hr₂.le p)
  have hmaj : Summable (fun p : ℤ × ℤ => A * (wt r₁ p.1 * wt r₂ p.2)) := hmul.mul_left A
  have hpt : ∀ p : ℤ × ℤ, ‖Work.KMTPlan.A6.coeff2 σ p.1 p.2‖ ≤ A * (wt r₁ p.1 * wt r₂ p.2) :=
    fun p => coeff2_le σ hper1 hper2 hsm r₁ r₂ A hr₁ hr₂ hA hder p.1 p.2
  have hsumm : Summable (fun p : ℤ × ℤ => ‖Work.KMTPlan.A6.coeff2 σ p.1 p.2‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => hpt p) hmaj
  have hle : (∑' p : ℤ × ℤ, ‖Work.KMTPlan.A6.coeff2 σ p.1 p.2‖)
      ≤ ∑' p : ℤ × ℤ, A * (wt r₁ p.1 * wt r₂ p.2) :=
    hsumm.tsum_le_tsum (fun p => hpt p) hmaj
  have hEq : (∑' p : ℤ × ℤ, A * (wt r₁ p.1 * wt r₂ p.2))
      = A * ((∑' p : ℤ, wt r₁ p) * (∑' p : ℤ, wt r₂ p)) := by
    rw [tsum_mul_left, ← hsum₁.tsum_mul_tsum hsum₂ hmul]
  have hb : A * ((∑' p : ℤ, wt r₁ p) * (∑' p : ℤ, wt r₂ p)) ≤ 40 * A := by
    have hA₁ : 0 ≤ ∑' p : ℤ, wt r₁ p := tsum_nonneg (fun p => wt_nonneg hr₁.le p)
    have hA₂ : 0 ≤ ∑' p : ℤ, wt r₂ p := tsum_nonneg (fun p => wt_nonneg hr₂.le p)
    have h16 : (∑' p : ℤ, wt r₁ p) * (∑' p : ℤ, wt r₂ p) ≤ 16 := by
      have h := mul_le_mul h4₁ h4₂ hA₂ (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    have h1 : A * ((∑' p : ℤ, wt r₁ p) * (∑' p : ℤ, wt r₂ p)) ≤ A * 16 :=
      mul_le_mul_of_nonneg_left h16 hA
    linarith [h1, hA]
  exact ⟨hsumm, hle.trans (hEq.le.trans hb)⟩

end Work.KMTPlan.A6
