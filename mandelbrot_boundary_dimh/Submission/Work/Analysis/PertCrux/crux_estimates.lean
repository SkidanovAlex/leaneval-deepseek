import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Analysis.PertCrux.landing_data_v3
import Submission.Work.Analysis.PertCrux.bounds_lambda_Rsc
import Submission.Work.Analysis.PertCrux.bounds_pert

namespace Work.Analysis.PertCrux

set_option maxHeartbeats 4000000

/-- If `1 ≤ x` then `x^a / x^b ≤ 1` for `a ≤ b`. -/
private lemma pow_div_pow_le_one {x : ℝ} (hx : (1:ℝ) ≤ x) {a b : ℕ} (h : a ≤ b) :
    x^a / x^b ≤ 1 := by
  rw [div_le_one (pow_pos (lt_of_lt_of_le zero_lt_one hx) b)]
  exact pow_le_pow_right₀ hx h

/-- If `10 ≤ x` then `x^a / x^b ≤ 10^{-(b-a)}` for `a ≤ b`. -/
private lemma pow_div_pow_le_inv_pow_ten {x : ℝ} (hx : (10:ℝ) ≤ x) {a b : ℕ} (hab : a ≤ b) :
    x^a / x^b ≤ 1/(10:ℝ)^(b-a) := by
  have hx0 : (0:ℝ) < x := by linarith
  have heq : x^a / x^b = 1/x^(b-a) := by
    rw [div_eq_div_iff (pow_ne_zero b (ne_of_gt hx0)) (pow_ne_zero (b-a) (ne_of_gt hx0))]
    rw [one_mul]
    conv_rhs => rw [← Nat.add_sub_of_le hab, pow_add]
  calc x^a / x^b = 1/x^(b-a) := heq
    _ ≤ 1/(10:ℝ)^(b-a) :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num) hx (b-a))

/-- Numeric core of `crux_estimates`: given the perturbation and bookkeeping
bounds produced by `bounds_pert` and `bounds_lambda_Rsc`, the six estimates hold. -/
private lemma crux_core {ρ₁ δ Ξ' MK Rgl εs Cgl dtau Rsc : ℝ} {u₀ α : ℂ} {m : ℕ}
    (hΞ' : 10 ≤ Ξ') (hδ : 0 < δ) (hρpos : 0 < ρ₁) (hρΞ : ρ₁ ≤ Ξ') (hδΞ : δ ≤ Ξ')
    (hCgl : 0 < Cgl) (hCglΞ : Cgl ≤ Ξ') (hMKΞ : MK ≤ Ξ') (hRglΞ : Rgl ≤ Ξ')
    (hRsc0 : 0 ≤ Rsc)
    (hαInF1 : |α.im| < α.re) (hαne : α ≠ 0)
    (hεss : εs ≤ δ / (10^9 * (Ξ'^2+1)^20))
    (hmB : (m:ℝ) ≤ 4.6*10^16*Ξ'^6)
    (hRsc1B : Rsc + 1 ≤ 4.7*10^16*Ξ'^6)
    (hdtauB : dtau ≤ 4.4*10^6*Ξ'^3)
    (hαB : ‖α‖ ≤ 2*Real.sqrt 2*ρ₁*δ/(10^50*(Ξ'^2+1)^100))
    (hαBs : ‖α‖ ≤ 2*Real.sqrt 2/(10^50*Ξ'^198))
    (hu1B : ‖u₀-1‖ ≤ 4*δ^2/(10^100*(Ξ'^2+1)^200) + Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*(Ξ'^2+1)^100)) :
    ‖u₀ - 1‖ ≤ 1 / 2 ∧
    64 * (‖u₀ - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1) ≤ min (1 / 2) (δ / (8 * Cgl)) ∧
    ‖α‖ * (Rsc + 1) ≤ 1 / 64 ∧
    (m : ℝ) + MK + dtau + Ξ' + 2 * Rgl + 4 ≤ (1 / α).re ∧
    εs * Rsc ^ 2 ≤ 1 / 4 ∧
    (Ξ' ^ 2 + 1) ^ 20 ≤ 1 / ‖α‖ := by
  have hΞ'pos : (0:ℝ) < Ξ' := by linarith
  have hΞ'1 : (1:ℝ) ≤ Ξ' := by linarith
  have hΞ'ne : Ξ' ≠ 0 := ne_of_gt hΞ'pos
  generalize hSdef : (Ξ'^2+1 : ℝ) = S at *
  have hSpos : (0:ℝ) < S := by rw [← hSdef]; positivity
  have hS1 : (1:ℝ) ≤ S := by rw [← hSdef]; nlinarith [sq_nonneg Ξ']
  have hXS : Ξ'^2 ≤ S := by rw [← hSdef]; linarith
  have hS400 : Ξ'^400 ≤ S^200 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Ξ'^2) hXS 200
    simpa [← pow_mul] using h
  have hS200 : Ξ'^200 ≤ S^100 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Ξ'^2) hXS 100
    simpa [← pow_mul] using h
  have hR0 : (0:ℝ) ≤ Rsc + 1 := by linarith
  have hs2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hδ2 : δ^2 ≤ Ξ'^2 := pow_le_pow_left₀ (le_of_lt hδ) hδΞ 2
  have hρδ : ρ₁*δ ≤ Ξ'*Ξ' := mul_le_mul hρΞ hδΞ (le_of_lt hδ) (le_of_lt hΞ'pos)
  have hX3 : Ξ'*ρ₁*δ ≤ Ξ'^3 := by
    have h2 : Ξ'*(ρ₁*δ) ≤ Ξ'*(Ξ'*Ξ') := mul_le_mul_of_nonneg_left hρδ (le_of_lt hΞ'pos)
    nlinarith [h2]
  -- ### hu1s
  have hu1s : ‖u₀-1‖ ≤ 1/(10^20*Ξ'^6) := by
    have ht1 : 4*δ^2/(10^100*S^200) ≤ 1/(2*(10^20*Ξ'^6)) := by
      have hs1 : 4*δ^2/(10^100*S^200) ≤ 4*Ξ'^2/(10^100*S^200) :=
        div_le_div_of_nonneg_right (by nlinarith [hδ2]) (by positivity)
      have hs2' : 4*Ξ'^2/(10^100*S^200) ≤ 4*Ξ'^2/(10^100*Ξ'^400) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [hS400]
      have hs4 : 4*Ξ'^2/(10^100*Ξ'^400) ≤ 1/(2*(10^20*Ξ'^6)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        rw [show (400:ℕ) = 8 + 392 by norm_num, pow_add]
        have hX392 : (1:ℝ) ≤ Ξ'^392 := one_le_pow₀ hΞ'1
        have hX8 : (0:ℝ) ≤ Ξ'^8 := by positivity
        nlinarith [hX392, hX8]
      exact le_trans hs1 (le_trans hs2' hs4)
    have ht2 : Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*S^100) ≤ 1/(2*(10^20*Ξ'^6)) := by
      have hnum : Real.sqrt 2*Ξ'*ρ₁*δ ≤ Real.sqrt 2*Ξ'^3 := by
        calc Real.sqrt 2*Ξ'*ρ₁*δ = Real.sqrt 2*(Ξ'*ρ₁*δ) := by ring
          _ ≤ Real.sqrt 2*Ξ'^3 := mul_le_mul_of_nonneg_left hX3 (Real.sqrt_nonneg 2)
      have hs1 : Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*S^100) ≤ Real.sqrt 2*Ξ'^3/(10^50*S^100) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      have hs2' : Real.sqrt 2*Ξ'^3/(10^50*S^100) ≤ Real.sqrt 2*Ξ'^3/(10^50*Ξ'^200) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [hS200]
      have hs4 : Real.sqrt 2*Ξ'^3/(10^50*Ξ'^200) ≤ 1/(2*(10^20*Ξ'^6)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        rw [show (200:ℕ) = 9 + 191 by norm_num, pow_add]
        have hX191 : (1:ℝ) ≤ Ξ'^191 := one_le_pow₀ hΞ'1
        have hX9 : (0:ℝ) ≤ Ξ'^9 := by positivity
        nlinarith [hX191, hs2, hX9, Real.sqrt_nonneg 2]
      exact le_trans hs1 (le_trans hs2' hs4)
    have hsum : 4*δ^2/(10^100*S^200) + Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*S^100) ≤ 1/(10^20*Ξ'^6) := by
      have h1 : (1:ℝ)/(2*(10^20*Ξ'^6)) + 1/(2*(10^20*Ξ'^6)) = 1/(10^20*Ξ'^6) := by
        field_simp
        ring
      linarith [ht1, ht2, h1]
    linarith [hu1B, hsum]
  -- ### hB1
  have hB1 : ‖α‖*(Rsc+1) ≤ 1/(10^30*Ξ'^192) := by
    have h1 : ‖α‖*(Rsc+1) ≤ (2*Real.sqrt 2/(10^50*Ξ'^198))*(4.7*10^16*Ξ'^6) :=
      mul_le_mul hαBs hRsc1B hR0 (by positivity)
    have h2 : (2*Real.sqrt 2/(10^50*Ξ'^198))*(4.7*10^16*Ξ'^6) ≤ 1/(10^30*Ξ'^192) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      rw [show (198:ℕ) = 6 + 192 by norm_num, pow_add]
      have hX6 : (0:ℝ) ≤ Ξ'^6 := by positivity
      have hX192 : (0:ℝ) ≤ Ξ'^192 := by positivity
      have hK : (2*Real.sqrt 2*(4.7*10^16)*10^30 : ℝ) ≤ 10^50 := by
        nlinarith [hs2, Real.sqrt_nonneg 2]
      calc (2*Real.sqrt 2*(4.7*10^16*Ξ'^6)*(10^30*Ξ'^192) : ℝ)
          = (2*Real.sqrt 2*(4.7*10^16)*10^30) * (Ξ'^6*Ξ'^192) := by ring
        _ ≤ 10^50 * (Ξ'^6*Ξ'^192) := mul_le_mul_of_nonneg_right hK (by positivity)
        _ = 1 * (10^50*(Ξ'^6*Ξ'^192)) := by ring
    linarith [h1, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- conjunct 1
    have hd2 : δ^2 ≤ S^200 := by
      have h2 : S ≤ S^200 := by
        have hh := pow_le_pow_right₀ hS1 (show (1:ℕ) ≤ 200 by norm_num)
        simpa using hh
      linarith [hδ2, hXS]
    have hA : 4*δ^2/(10^100*S^200) ≤ 1/4 := by
      rw [div_le_iff₀ (by positivity)]
      have hc : (16:ℝ) ≤ 10^100 := by norm_num
      have hSn' : (0:ℝ) ≤ S^200 := pow_nonneg (le_of_lt hSpos) 200
      have h2 : (16:ℝ)*S^200 ≤ 10^100 * S^200 := mul_le_mul_of_nonneg_right hc hSn'
      nlinarith [hd2, h2]
    have hB : Real.sqrt 2 * Ξ' * ρ₁ * δ / (10^50*S^100) ≤ 1/4 := by
      have hnum : Real.sqrt 2 * Ξ' * ρ₁ * δ ≤ 2 * Ξ'^3 := by
        calc Real.sqrt 2 * Ξ' * ρ₁ * δ = Real.sqrt 2 * (Ξ'*ρ₁*δ) := by ring
          _ ≤ 2 * (Ξ'*ρ₁*δ) := mul_le_mul_of_nonneg_right hs2 (by positivity)
          _ ≤ 2 * Ξ'^3 := mul_le_mul_of_nonneg_left hX3 (by norm_num)
      have hden : (2 * Ξ'^3) / (10^50 * Ξ'^200) ≤ 1/4 := by
        rw [div_le_iff₀ (by positivity)]
        rw [show (200:ℕ) = 197 + 3 by norm_num, pow_add]
        have hX197 : (1:ℝ) ≤ Ξ'^197 := one_le_pow₀ hΞ'1
        have hX3' : (0:ℝ) ≤ Ξ'^3 := by positivity
        nlinarith [hX197, hX3']
      calc Real.sqrt 2 * Ξ' * ρ₁ * δ / (10^50*S^100)
          ≤ (2*Ξ'^3)/(10^50*S^100) := div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ (2*Ξ'^3)/(10^50*Ξ'^200) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith [hS200]
        _ ≤ 1/4 := hden
    linarith [hu1B, hA, hB]
  · -- conjunct 2
    have hI1 : 64*‖u₀-1‖*(Rsc+1) ≤ 1/4 := by
      have h1 : 64*‖u₀-1‖*(Rsc+1) ≤ 64*(1/(10^20*Ξ'^6))*(4.7*10^16*Ξ'^6) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hu1s (by norm_num)) hRsc1B hR0 (by positivity)
      have h2 : 64*(1/(10^20*Ξ'^6))*(4.7*10^16*Ξ'^6) ≤ 1/4 := by
        have heq : 64*(1/(10^20*Ξ'^6))*(4.7*10^16*Ξ'^6) = 64*4.7*10^16/10^20 := by
          field_simp
        rw [heq]; norm_num
      linarith [h1, h2]
    have hI2 : 64*(‖α‖*(Rsc+1))*(Rsc+1) ≤ 1/4 := by
      have h1 : 64*(‖α‖*(Rsc+1))*(Rsc+1) ≤ 64*(1/(10^30*Ξ'^192))*(4.7*10^16*Ξ'^6) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB1 (by norm_num)) hRsc1B hR0 (by positivity)
      have h2 : 64*(1/(10^30*Ξ'^192))*(4.7*10^16*Ξ'^6) ≤ 1/4 := by
        have heq : 64*(1/(10^30*Ξ'^192))*(4.7*10^16*Ξ'^6)
            = (64*4.7*10^16/10^30) * (1/Ξ'^186) := by
          rw [show (192:ℕ) = 186 + 6 by norm_num, pow_add]
          field_simp
        rw [heq]
        have h3 : (1:ℝ)/Ξ'^186 ≤ 1 := by
          rw [div_le_one (by positivity)]; exact one_le_pow₀ hΞ'1
        have h4 : (64*4.7*10^16/10^30 : ℝ) ≤ 1/4 := by norm_num
        have h50 : (0:ℝ) ≤ 64*4.7*10^16/10^30 := by norm_num
        have h60 : (0:ℝ) ≤ 1/Ξ'^186 := by positivity
        nlinarith [h3, h4, h50, h60]
      linarith [h1, h2]
    have hIE : 64*(‖u₀-1‖ + ‖α‖*(Rsc+1))*(Rsc+1)
        = 64*‖u₀-1‖*(Rsc+1) + 64*(‖α‖*(Rsc+1))*(Rsc+1) := by ring
    have hIP1 : 64*(‖u₀-1‖ + ‖α‖*(Rsc+1))*(Rsc+1) ≤ 1/2 := by
      linarith [hIE.le, hIE.ge, hI1, hI2]
    -- part 2
    have hGa : 512*Ξ'*(4*δ^2/(10^100*S^200))*(Rsc+1) ≤ δ/3 := by
      have hδ2' : δ^2 ≤ δ*Ξ' := by nlinarith [hδ, hδΞ]
      have e1 : 512*Ξ'*(4*δ^2/(10^100*S^200))*(Rsc+1)
          ≤ 512*Ξ'*(4*(δ*Ξ')/(10^100*Ξ'^400))*(4.7*10^16*Ξ'^6) := by
        have hA : 4*δ^2/(10^100*S^200) ≤ 4*(δ*Ξ')/(10^100*Ξ'^400) := by
          have hs1 : 4*δ^2/(10^100*S^200) ≤ 4*(δ*Ξ')/(10^100*S^200) :=
            div_le_div_of_nonneg_right (by nlinarith [hδ2']) (by positivity)
          have hs2' : 4*(δ*Ξ')/(10^100*S^200) ≤ 4*(δ*Ξ')/(10^100*Ξ'^400) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith [hS400]
          exact le_trans hs1 hs2'
        exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity)) hRsc1B hR0 (by positivity)
      have e2 : 512*Ξ'*(4*(δ*Ξ')/(10^100*Ξ'^400))*(4.7*10^16*Ξ'^6)
          = δ * (512*4*4.7*10^16/10^100) * (Ξ'^8/Ξ'^400) := by
        rw [show (400:ℕ) = 392 + 8 by norm_num, pow_add]
        field_simp
      have e3 : δ * (512*4*4.7*10^16/10^100) * (Ξ'^8/Ξ'^400) ≤ δ/3 := by
        have hK : (512*4*4.7*10^16/10^100 : ℝ) ≤ 1/3 := by norm_num
        have hQ : Ξ'^8/Ξ'^400 ≤ 1 := pow_div_pow_le_one hΞ'1 (by norm_num : 8 ≤ 400)
        have hQ0 : (0:ℝ) ≤ Ξ'^8/Ξ'^400 := by positivity
        have hK0 : (0:ℝ) ≤ 512*4*4.7*10^16/10^100 := by norm_num
        have hδ0 : (0:ℝ) ≤ δ := le_of_lt hδ
        have hKQ : (512*4*4.7*10^16/10^100) * (Ξ'^8/Ξ'^400) ≤ 1/3 := by
          calc _ ≤ (1/3)*1 := mul_le_mul hK hQ hQ0 (by norm_num)
            _ = 1/3 := by norm_num
        calc δ * (512*4*4.7*10^16/10^100) * (Ξ'^8/Ξ'^400)
            = δ * ((512*4*4.7*10^16/10^100) * (Ξ'^8/Ξ'^400)) := by ring
          _ ≤ δ * (1/3) := mul_le_mul_of_nonneg_left hKQ hδ0
          _ = δ/3 := by ring
      linarith [e1, e2.le, e2.ge, e3]
    have hGb : 512*Ξ'*(Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*S^100))*(Rsc+1) ≤ δ/3 := by
      have e1 : 512*Ξ'*(Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*S^100))*(Rsc+1)
          ≤ 512*Ξ'*(Real.sqrt 2*(Ξ'*Ξ')*δ/(10^50*Ξ'^200))*(4.7*10^16*Ξ'^6) := by
        have hA : Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*S^100) ≤ Real.sqrt 2*(Ξ'*Ξ')*δ/(10^50*Ξ'^200) := by
          have hs1 : Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*S^100) ≤ Real.sqrt 2*(Ξ'*Ξ')*δ/(10^50*S^100) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            have h2' : Real.sqrt 2*Ξ'*δ*ρ₁ ≤ Real.sqrt 2*Ξ'*δ*Ξ' :=
              mul_le_mul_of_nonneg_left hρΞ (by positivity)
            linarith [h2']
          have hs2' : Real.sqrt 2*(Ξ'*Ξ')*δ/(10^50*S^100) ≤ Real.sqrt 2*(Ξ'*Ξ')*δ/(10^50*Ξ'^200) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith [hS200]
          exact le_trans hs1 hs2'
        exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity)) hRsc1B hR0 (by positivity)
      have e2 : 512*Ξ'*(Real.sqrt 2*(Ξ'*Ξ')*δ/(10^50*Ξ'^200))*(4.7*10^16*Ξ'^6)
          = δ * (512*Real.sqrt 2*4.7*10^16/10^50) * (Ξ'^9/Ξ'^200) := by
        rw [show (200:ℕ) = 191 + 9 by norm_num, pow_add]
        field_simp
      have e3 : δ * (512*Real.sqrt 2*4.7*10^16/10^50) * (Ξ'^9/Ξ'^200) ≤ δ/3 := by
        have hK : (512*Real.sqrt 2*4.7*10^16/10^50 : ℝ) ≤ 1/3 := by
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10^50)]
          nlinarith [hs2, Real.sqrt_nonneg 2]
        have hQ : Ξ'^9/Ξ'^200 ≤ 1 := pow_div_pow_le_one hΞ'1 (by norm_num : 9 ≤ 200)
        have hQ0 : (0:ℝ) ≤ Ξ'^9/Ξ'^200 := by positivity
        have hK0 : (0:ℝ) ≤ 512*Real.sqrt 2*4.7*10^16/10^50 := by positivity
        have hδ0 : (0:ℝ) ≤ δ := le_of_lt hδ
        have hKQ : (512*Real.sqrt 2*4.7*10^16/10^50) * (Ξ'^9/Ξ'^200) ≤ 1/3 := by
          calc _ ≤ (1/3)*1 := mul_le_mul hK hQ hQ0 (by norm_num)
            _ = 1/3 := by norm_num
        calc δ * (512*Real.sqrt 2*4.7*10^16/10^50) * (Ξ'^9/Ξ'^200)
            = δ * ((512*Real.sqrt 2*4.7*10^16/10^50) * (Ξ'^9/Ξ'^200)) := by ring
          _ ≤ δ * (1/3) := mul_le_mul_of_nonneg_left hKQ hδ0
          _ = δ/3 := by ring
      linarith [e1, e2.le, e2.ge, e3]
    have hGc : 512*Ξ'*(‖α‖*(Rsc+1))*(Rsc+1) ≤ δ/3 := by
      have e1 : 512*Ξ'*(‖α‖*(Rsc+1))*(Rsc+1)
          ≤ 512*Ξ'*((2*Real.sqrt 2*ρ₁*δ/(10^50*S^100))*(4.7*10^16*Ξ'^6))*(Rsc+1) := by
        have hA : ‖α‖*(Rsc+1) ≤ (2*Real.sqrt 2*ρ₁*δ/(10^50*S^100))*(4.7*10^16*Ξ'^6) :=
          mul_le_mul hαB hRsc1B hR0 (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity)) (le_refl _) hR0 (by positivity)
      have e2 : 512*Ξ'*((2*Real.sqrt 2*ρ₁*δ/(10^50*S^100))*(4.7*10^16*Ξ'^6))*(Rsc+1)
          ≤ 512*Ξ'*((2*Real.sqrt 2*(Ξ')*δ/(10^50*Ξ'^200))*(4.7*10^16*Ξ'^6))*(4.7*10^16*Ξ'^6) := by
        have hA : (2*Real.sqrt 2*ρ₁*δ/(10^50*S^100))*(4.7*10^16*Ξ'^6)
            ≤ (2*Real.sqrt 2*(Ξ')*δ/(10^50*Ξ'^200))*(4.7*10^16*Ξ'^6) := by
          have hs1 : 2*Real.sqrt 2*ρ₁*δ/(10^50*S^100) ≤ 2*Real.sqrt 2*(Ξ')*δ/(10^50*S^100) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            have h2' : 2*Real.sqrt 2*δ*ρ₁ ≤ 2*Real.sqrt 2*δ*Ξ' :=
              mul_le_mul_of_nonneg_left hρΞ (by positivity)
            linarith [h2']
          have hs2' : 2*Real.sqrt 2*(Ξ')*δ/(10^50*S^100) ≤ 2*Real.sqrt 2*(Ξ')*δ/(10^50*Ξ'^200) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith [hS200]
          exact mul_le_mul_of_nonneg_right (le_trans hs1 hs2') (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity)) hRsc1B hR0 (by positivity)
      have e3 : 512*Ξ'*((2*Real.sqrt 2*(Ξ')*δ/(10^50*Ξ'^200))*(4.7*10^16*Ξ'^6))*(4.7*10^16*Ξ'^6)
          = δ * (512*2*Real.sqrt 2*(4.7*10^16)^2/10^50) * (Ξ'^14/Ξ'^200) := by
        rw [show (200:ℕ) = 186 + 14 by norm_num, pow_add]
        field_simp
      have e4 : δ * (512*2*Real.sqrt 2*(4.7*10^16)^2/10^50) * (Ξ'^14/Ξ'^200) ≤ δ/3 := by
        have hK : (512*2*Real.sqrt 2*(4.7*10^16)^2/10^50 : ℝ) ≤ 1/3 := by
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10^50)]
          nlinarith [hs2, Real.sqrt_nonneg 2]
        have hQ : Ξ'^14/Ξ'^200 ≤ 1 := pow_div_pow_le_one hΞ'1 (by norm_num : 14 ≤ 200)
        have hQ0 : (0:ℝ) ≤ Ξ'^14/Ξ'^200 := by positivity
        have hK0 : (0:ℝ) ≤ 512*2*Real.sqrt 2*(4.7*10^16)^2/10^50 := by positivity
        have hδ0 : (0:ℝ) ≤ δ := le_of_lt hδ
        have hKQ : (512*2*Real.sqrt 2*(4.7*10^16)^2/10^50) * (Ξ'^14/Ξ'^200) ≤ 1/3 := by
          calc _ ≤ (1/3)*1 := mul_le_mul hK hQ hQ0 (by norm_num)
            _ = 1/3 := by norm_num
        calc δ * (512*2*Real.sqrt 2*(4.7*10^16)^2/10^50) * (Ξ'^14/Ξ'^200)
            = δ * ((512*2*Real.sqrt 2*(4.7*10^16)^2/10^50) * (Ξ'^14/Ξ'^200)) := by ring
          _ ≤ δ * (1/3) := mul_le_mul_of_nonneg_left hKQ hδ0
          _ = δ/3 := by ring
      linarith [e1, e2, e3.le, e3.ge, e4]
    have hGE : 512*Ξ'*(‖u₀-1‖ + ‖α‖*(Rsc+1))*(Rsc+1)
        = 512*Ξ'*‖u₀-1‖*(Rsc+1) + 512*Ξ'*(‖α‖*(Rsc+1))*(Rsc+1) := by ring
    have hGu : 512*Ξ'*‖u₀-1‖*(Rsc+1) ≤ 2*δ/3 := by
      have h1 : 512*Ξ'*‖u₀-1‖*(Rsc+1)
          ≤ 512*Ξ'*(4*δ^2/(10^100*S^200) + Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*S^100))*(Rsc+1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hu1B (by positivity)) (le_refl _) hR0 (by positivity)
      have h2 : 512*Ξ'*(4*δ^2/(10^100*S^200) + Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*S^100))*(Rsc+1)
          = 512*Ξ'*(4*δ^2/(10^100*S^200))*(Rsc+1)
            + 512*Ξ'*(Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*S^100))*(Rsc+1) := by ring
      linarith [h1, h2.le, h2.ge, hGa, hGb]
    have hG : 512*Ξ'*(‖u₀-1‖ + ‖α‖*(Rsc+1))*(Rsc+1) ≤ δ := by
      linarith [hGE.le, hGE.ge, hGu, hGc]
    have hX : 64*(‖u₀-1‖ + ‖α‖*(Rsc+1))*(Rsc+1) ≤ δ/(8*Ξ') := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hG]
    have hX2 : δ/(8*Ξ') ≤ δ/(8*Cgl) := by
      apply div_le_div_of_nonneg_left (le_of_lt hδ) (by positivity)
      linarith [hCglΞ]
    exact le_min hIP1 (le_trans hX hX2)
  · -- conjunct 3
    have h1 : ‖α‖*(Rsc+1) ≤ (2*Real.sqrt 2/(10^50*Ξ'^198))*(4.7*10^16*Ξ'^6) :=
      mul_le_mul hαBs hRsc1B hR0 (by positivity)
    have h2 : (2*Real.sqrt 2/(10^50*Ξ'^198))*(4.7*10^16*Ξ'^6) ≤ 1/64 := by
      have heq : (2*Real.sqrt 2/(10^50*Ξ'^198))*(4.7*10^16*Ξ'^6)
          = (2*Real.sqrt 2*4.7*10^16/10^50) * (Ξ'^6/Ξ'^198) := by
        rw [show (198:ℕ) = 6 + 192 by norm_num, pow_add]
        field_simp
      rw [heq]
      have h3 : Ξ'^6/Ξ'^198 ≤ 1 := pow_div_pow_le_one hΞ'1 (by norm_num : 6 ≤ 198)
      have hK : (2*Real.sqrt 2*4.7*10^16/10^50 : ℝ) ≤ 1/64 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10^50)]
        nlinarith [hs2, Real.sqrt_nonneg 2]
      have h50 : (0:ℝ) ≤ 2*Real.sqrt 2*4.7*10^16/10^50 := by positivity
      have h60 : (0:ℝ) ≤ Ξ'^6/Ξ'^198 := by positivity
      calc (2*Real.sqrt 2*4.7*10^16/10^50) * (Ξ'^6/Ξ'^198) ≤ (1/64)*1 :=
              mul_le_mul hK h3 h60 (by norm_num)
        _ = 1/64 := by norm_num
    linarith [h1, h2]
  · -- conjunct 4
    have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
    have hre : 1/(2*‖α‖) ≤ (1/α).re := by
      have hrepos : (0:ℝ) < α.re := lt_of_le_of_lt (abs_nonneg _) hαInF1
      have him2 : α.im^2 < α.re^2 := by
        rw [sq_lt_sq, abs_of_nonneg hrepos.le]
        exact hαInF1
      have hnsq : Complex.normSq α = α.re^2 + α.im^2 := by rw [Complex.normSq_apply]; ring
      have hlt : Complex.normSq α < 2*α.re^2 := by rw [hnsq]; linarith
      have hnsqpos : (0:ℝ) < Complex.normSq α := Complex.normSq_pos.mpr hαne
      have hinv : (1/α).re = α.re/Complex.normSq α := by rw [one_div, Complex.inv_re]
      have hstep1 : α.re/(2*α.re^2) < (1/α).re := by
        rw [hinv, div_lt_div_iff₀ (by positivity) hnsqpos]
        nlinarith [hlt, hrepos]
      have hstep2 : α.re/(2*α.re^2) = 1/(2*α.re) := by field_simp
      have hstep3 : (1:ℝ)/(2*‖α‖) ≤ 1/(2*α.re) :=
        one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2*α.re)
          (by linarith [Complex.re_le_norm α])
      linarith [hstep1, hstep2.le, hstep2.ge, hstep3]
    have hbig : (m:ℝ) + MK + dtau + Ξ' + 2*Rgl + 4 ≤ 4.7*10^16*Ξ'^6 := by
      have hX3le6 : Ξ'^3 ≤ Ξ'^6 := pow_le_pow_right₀ hΞ'1 (by norm_num : (3:ℕ) ≤ 6)
      have hXle6 : Ξ' ≤ Ξ'^6 := by
        have hh := pow_le_pow_right₀ hΞ'1 (show (1:ℕ) ≤ 6 by norm_num)
        simpa using hh
      nlinarith [hmB, hdtauB, hMKΞ, hRglΞ, hX3le6, hXle6]
    have hstep : (4.7*10^16*Ξ'^6 : ℝ) ≤ 1/(2*‖α‖) := by
      have hα2 : 2*‖α‖ ≤ 2*(2*Real.sqrt 2/(10^50*Ξ'^198)) := by linarith [hαBs]
      have h1 : 1/(2*(2*Real.sqrt 2/(10^50*Ξ'^198))) ≤ 1/(2*‖α‖) := by
        exact one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2*‖α‖) hα2
      have h2 : (4.7*10^16*Ξ'^6 : ℝ) ≤ 1/(2*(2*Real.sqrt 2/(10^50*Ξ'^198))) := by
        have heq : 2*(2*Real.sqrt 2/(10^50*Ξ'^198)) = 4*Real.sqrt 2/(10^50*Ξ'^198) := by ring
        rw [heq, one_div, inv_div, le_div_iff₀ (by positivity)]
        rw [show (198:ℕ) = 192 + 6 by norm_num, pow_add]
        have hX192 : (1:ℝ) ≤ Ξ'^192 := one_le_pow₀ hΞ'1
        have hX6 : (0:ℝ) ≤ Ξ'^6 := by positivity
        nlinarith [hX192, hs2, hX6, Real.sqrt_nonneg 2]
      linarith [h1, h2]
    linarith [hre, hbig, hstep]
  · -- conjunct 5
    have hRsc_ub : Rsc ≤ 4.7*10^16*Ξ'^6 := by linarith [hRsc1B]
    have hRsc2 : Rsc^2 ≤ (4.7*10^16*Ξ'^6)^2 := pow_le_pow_left₀ hRsc0 hRsc_ub 2
    have hεs2 : εs ≤ Ξ'/(10^9*S^20) := by
      have h := div_le_div_of_nonneg_right hδΞ (by positivity : (0:ℝ) ≤ 10^9*S^20)
      linarith [hεss, h]
    have h1 : εs*Rsc^2 ≤ (Ξ'/(10^9*S^20)) * (4.7*10^16*Ξ'^6)^2 :=
      mul_le_mul hεs2 hRsc2 (by positivity) (by positivity)
    have h2 : (Ξ'/(10^9*S^20)) * (4.7*10^16*Ξ'^6)^2 ≤ 1/4 := by
      have hS40 : Ξ'^40 ≤ S^20 := by
        have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Ξ'^2) hXS 20
        simpa [← pow_mul] using h
      have hA : Ξ'/(10^9*S^20) ≤ Ξ'/(10^9*Ξ'^40) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith [hS40]
      have hB : (Ξ'/(10^9*Ξ'^40)) * (4.7*10^16*Ξ'^6)^2 ≤ 1/4 := by
        have heq : (Ξ'/(10^9*Ξ'^40)) * (4.7*10^16*Ξ'^6)^2
            = ((4.7*10^16)^2/10^9) * (Ξ'^13/Ξ'^40) := by
          rw [show (40:ℕ) = 13 + 27 by norm_num, pow_add]
          field_simp
        rw [heq]
        have h3 : Ξ'^13/Ξ'^40 ≤ 1/(10:ℝ)^27 := pow_div_pow_le_inv_pow_ten hΞ' (by norm_num : 13 ≤ 40)
        have h4 : ((4.7*10^16)^2/10^9 * (1/(10:ℝ)^27) : ℝ) ≤ 1/4 := by norm_num
        have h50 : (0:ℝ) ≤ (4.7*10^16)^2/10^9 := by norm_num
        have h60 : (0:ℝ) ≤ Ξ'^13/Ξ'^40 := by positivity
        nlinarith [h3, h4, h50, h60]
      have hC : (Ξ'/(10^9*S^20)) * (4.7*10^16*Ξ'^6)^2
          ≤ (Ξ'/(10^9*Ξ'^40)) * (4.7*10^16*Ξ'^6)^2 :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      linarith [hC, hB]
    linarith [h1, h2]
  · -- conjunct 6
    have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
    rw [le_div_iff₀ hαpos]
    have hS20 : S^20 ≤ 2^20 * Ξ'^40 := by
      have hle : S ≤ 2*Ξ'^2 := by rw [← hSdef]; nlinarith [hΞ'1, sq_nonneg (Ξ'-1)]
      have h := pow_le_pow_left₀ (le_of_lt hSpos) hle 20
      calc S^20 ≤ (2*Ξ'^2)^20 := h
        _ = 2^20 * Ξ'^40 := by rw [mul_pow]; ring_nf
    have h1 : S^20 * ‖α‖ ≤ (2^20*Ξ'^40) * (2*Real.sqrt 2/(10^50*Ξ'^198)) :=
      mul_le_mul hS20 hαBs (le_of_lt hαpos) (by positivity)
    have h2 : (2^20*Ξ'^40) * (2*Real.sqrt 2/(10^50*Ξ'^198)) ≤ 1 := by
      have heq : (2^20*Ξ'^40) * (2*Real.sqrt 2/(10^50*Ξ'^198))
          = (2^20*2*Real.sqrt 2/10^50) * (Ξ'^40/Ξ'^198) := by
        rw [show (198:ℕ) = 40 + 158 by norm_num, pow_add]
        field_simp
      rw [heq]
      have h3 : Ξ'^40/Ξ'^198 ≤ 1 := pow_div_pow_le_one hΞ'1 (by norm_num : 40 ≤ 198)
      have hK : (2^20*2*Real.sqrt 2/10^50 : ℝ) ≤ 1 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10^50)]
        nlinarith [hs2, Real.sqrt_nonneg 2]
      have h50 : (0:ℝ) ≤ 2^20*2*Real.sqrt 2/10^50 := by positivity
      have h60 : (0:ℝ) ≤ Ξ'^40/Ξ'^198 := by positivity
      calc (2^20*2*Real.sqrt 2/10^50) * (Ξ'^40/Ξ'^198) ≤ 1 * 1 :=
              mul_le_mul hK h3 h60 (by norm_num)
        _ = 1 := by norm_num
    linarith [h1, h2]


theorem crux_estimates
    {δ₀ ρ₁ δ Ξ' M₀ MK CW Rgl εs Cgl Λ : ℝ} {u₀ α : ℂ} {m : ℕ} {dtau Rsc : ℝ}
    (hδ : 0 < δ) (hCgl : 0 < Cgl) (hΞ' : 10 ≤ Ξ')
    (hM₀ : 0 ≤ M₀) (hMK : 0 ≤ MK) (hCW : 0 ≤ CW) (hRgl : 0 ≤ Rgl)
    (hM₀Ξ : M₀ ≤ Ξ') (hρ₁pos : 0 < ρ₁) (hρ₁Ξ : ρ₁ ≤ Ξ') (hδΞ : δ ≤ Ξ')
    (hMKΞ : MK ≤ Ξ') (hCWΞ : CW ≤ Ξ') (hRglΞ : Rgl ≤ Ξ') (hCglΞ : Cgl ≤ Ξ')
    (hΛ64 : 64 ≤ Λ) (hΛΞ : Ξ' ≤ Λ) (hΛMK : MK ≤ Λ) (hΛCW : CW ≤ Λ) (hΛRgl : Rgl ≤ Λ / 8)
    (hΛUB : Λ ≤ 10 ^ 6 * (Ξ' + MK + CW + Rgl + 1) ^ 3 + 10 ^ 6)
    (hdtau0 : 0 ≤ dtau) (hdtauΛ : dtau ≤ Λ / 16)
    (hRsc0 : 0 ≤ Rsc) (hRscUB : Rsc ≤ (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 + MK + Λ + 4)
    (hmUB : (m : ℝ) ≤ (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 + 2)
    (hmge : Ξ' + Λ ≤ (m : ℝ))
    (hδ₀tiny : δ₀ ≤ ρ₁ ^ 2 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200))
    (hu1 : ‖u₀ - 1‖ ≤ 4 * δ₀ / ρ₁ ^ 2 + M₀ * Real.sqrt (2 * δ₀))
    (hαle : ‖α‖ ≤ 2 * Real.sqrt (2 * δ₀))
    (hαInF1 : |α.im| < α.re) (hαne : α ≠ 0)
    (hεs0 : 0 < εs) (hεss : εs ≤ δ / (10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20)) :
    ‖u₀ - 1‖ ≤ 1 / 2 ∧
    64 * (‖u₀ - 1‖ + ‖α‖ * (Rsc + 1)) * (Rsc + 1) ≤ min (1 / 2) (δ / (8 * Cgl)) ∧
    ‖α‖ * (Rsc + 1) ≤ 1 / 64 ∧
    (m : ℝ) + MK + dtau + Ξ' + 2 * Rgl + 4 ≤ (1 / α).re ∧
    εs * Rsc ^ 2 ≤ 1 / 4 ∧
    (Ξ' ^ 2 + 1) ^ 20 ≤ 1 / ‖α‖ := by
  have hmB : (m:ℝ) ≤ 4.6*10^16*Ξ'^6 :=
    (bounds_lambda_Rsc hΞ' hMKΞ hCWΞ hRglΞ hΛ64 hΛUB hdtauΛ hRscUB hmUB).2.1
  have hRsc1B : Rsc + 1 ≤ 4.7*10^16*Ξ'^6 :=
    (bounds_lambda_Rsc hΞ' hMKΞ hCWΞ hRglΞ hΛ64 hΛUB hdtauΛ hRscUB hmUB).2.2.1
  have hdtauB : dtau ≤ 4.4*10^6*Ξ'^3 :=
    (bounds_lambda_Rsc hΞ' hMKΞ hCWΞ hRglΞ hΛ64 hΛUB hdtauΛ hRscUB hmUB).2.2.2
  have hαB : ‖α‖ ≤ 2*Real.sqrt 2*ρ₁*δ/(10^50*(Ξ'^2+1)^100) :=
    (bounds_pert hΞ' hδ hρ₁pos hρ₁Ξ hδΞ hM₀ hM₀Ξ hδ₀tiny hu1 hαle).1
  have hαBs : ‖α‖ ≤ 2*Real.sqrt 2/(10^50*Ξ'^198) :=
    (bounds_pert hΞ' hδ hρ₁pos hρ₁Ξ hδΞ hM₀ hM₀Ξ hδ₀tiny hu1 hαle).2.1
  have hu1B : ‖u₀-1‖ ≤ 4*δ^2/(10^100*(Ξ'^2+1)^200)
      + Real.sqrt 2*Ξ'*ρ₁*δ/(10^50*(Ξ'^2+1)^100) :=
    (bounds_pert hΞ' hδ hρ₁pos hρ₁Ξ hδΞ hM₀ hM₀Ξ hδ₀tiny hu1 hαle).2.2
  exact crux_core hΞ' hδ hρ₁pos hρ₁Ξ hδΞ hCgl hCglΞ hMKΞ hRglΞ hRsc0 hαInF1 hαne hεss
    hmB hRsc1B hdtauB hαB hαBs hu1B

end Work.Analysis.PertCrux
