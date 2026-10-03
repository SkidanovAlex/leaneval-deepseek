import Mathlib

namespace Work.FIArea6Hecke.R

/-- Quantitative version of "the logarithm is dominated by every positive power":
for `x ≥ 1`, `k ≥ 0` and `δ > 0` one has `(log x)^k ≤ ((k+1)/δ)^k x^δ`.

It follows from `Real.log_le_rpow_div` applied with exponent `δ/(k+1)`, namely
`log x ≤ x^(δ/(k+1)) / (δ/(k+1)) = ((k+1)/δ) x^(δ/(k+1))`, then raising to the
power `k` and using that `δ/(k+1) * k ≤ δ`. -/
lemma logRpow_le_mul_rpow (k δ : ℝ) (hk : 0 ≤ k) (hδ : 0 < δ) :
    ∀ x : ℝ, 1 ≤ x → (Real.log x) ^ k ≤ ((k + 1) / δ) ^ k * x ^ δ := by
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  have hk1 : 0 < k + 1 := by linarith
  have hc : 0 < δ / (k + 1) := div_pos hδ hk1
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : Real.log x ≤ ((k + 1) / δ) * x ^ (δ / (k + 1)) := by
    have h := Real.log_le_rpow_div (x := x) (ε := δ / (k + 1)) hx0 hc
    rw [div_eq_mul_inv, inv_div, mul_comm] at h
    exact h
  have h2 : (Real.log x) ^ k ≤ (((k + 1) / δ) * x ^ (δ / (k + 1))) ^ k :=
    Real.rpow_le_rpow hlog_nn h1 hk
  have h3 : (((k + 1) / δ) * x ^ (δ / (k + 1))) ^ k
      = ((k + 1) / δ) ^ k * x ^ (δ / (k + 1) * k) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hx0 _), ← Real.rpow_mul hx0]
  have hexp : δ / (k + 1) * k ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hk1]
    nlinarith [hk, hδ]
  have h4 : x ^ (δ / (k + 1) * k) ≤ x ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hx hexp
  calc (Real.log x) ^ k
      ≤ (((k + 1) / δ) * x ^ (δ / (k + 1))) ^ k := h2
    _ = ((k + 1) / δ) ^ k * x ^ (δ / (k + 1) * k) := h3
    _ ≤ ((k + 1) / δ) ^ k * x ^ δ :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

theorem logRpowAbsorb (ε : ℝ) (hε : 0 < ε) (ks kd : ℝ) (hks : 0 ≤ ks) (hkd : 0 ≤ kd)
    (Cs Cd : ℝ) (hCs : 0 < Cs) (hCd : 0 < Cd) (d₁ : ℕ) (hd₁ : 1 ≤ d₁) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ d : ℕ, 1 ≤ d →
      Cs * (Real.log (8 * (d₁ : ℝ) * (d : ℝ))) ^ ks ≤ A * (d : ℝ) ^ (ε / 400) ∧
      Cd * (2 * (d : ℝ)) ^ (ε / 4) * (Real.log (8 * (d : ℝ))) ^ kd
        ≤ A * (d : ℝ) ^ (3 * ε / 8) := by
  have hδ1 : 0 < ε / 400 := by positivity
  have hδ2 : 0 < ε / 8 := by positivity
  set A₁ : ℝ := Cs * ((ks + 1) / (ε / 400)) ^ ks * (8 * (d₁ : ℝ)) ^ (ε / 400) with hA₁
  set A₂ : ℝ := Cd * (2:ℝ) ^ (ε / 4) * ((kd + 1) / (ε / 8)) ^ kd * (8:ℝ) ^ (ε / 8) with hA₂
  refine ⟨max 1 (max A₁ A₂), le_max_left _ _, ?_⟩
  intro d hd
  have hd₁R : (1:ℝ) ≤ (d₁:ℝ) := by exact_mod_cast hd₁
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hd0 : (0:ℝ) ≤ (d:ℝ) := by linarith
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hAle1 : A₁ ≤ max 1 (max A₁ A₂) :=
    le_trans (le_max_left A₁ A₂) (le_max_right 1 (max A₁ A₂))
  have hAle2 : A₂ ≤ max 1 (max A₁ A₂) :=
    le_trans (le_max_right A₁ A₂) (le_max_right 1 (max A₁ A₂))
  constructor
  · have hx1 : (1:ℝ) ≤ 8 * (d₁:ℝ) * (d:ℝ) := by nlinarith [hd₁R, hdR]
    have h1 := logRpow_le_mul_rpow ks (ε/400) hks hδ1 (8 * (d₁:ℝ) * (d:ℝ)) hx1
    have hsplit : (8 * (d₁:ℝ) * (d:ℝ))^(ε/400)
        = (8 * (d₁:ℝ))^(ε/400) * (d:ℝ)^(ε/400) :=
      Real.mul_rpow (by positivity) (by positivity)
    rw [hsplit] at h1
    have hcore : Cs * (Real.log (8 * (d₁:ℝ) * (d:ℝ))) ^ ks ≤ A₁ * (d:ℝ)^(ε/400) := by
      rw [hA₁]
      calc Cs * (Real.log (8 * (d₁:ℝ) * (d:ℝ))) ^ ks
          ≤ Cs * (((ks + 1) / (ε/400)) ^ ks
                * ((8 * (d₁:ℝ)) ^ (ε/400) * (d:ℝ) ^ (ε/400))) :=
            mul_le_mul_of_nonneg_left h1 hCs.le
        _ = (Cs * ((ks + 1) / (ε/400)) ^ ks * (8 * (d₁:ℝ)) ^ (ε/400)) * (d:ℝ) ^ (ε/400) := by ring
    exact hcore.trans (mul_le_mul_of_nonneg_right hAle1 (by positivity))
  · have hy1 : (1:ℝ) ≤ 8 * (d:ℝ) := by nlinarith [hdR]
    have h2 := logRpow_le_mul_rpow kd (ε/8) hkd hδ2 (8 * (d:ℝ)) hy1
    have hsplit2 : (8 * (d:ℝ))^(ε/8) = (8:ℝ)^(ε/8) * (d:ℝ)^(ε/8) :=
      Real.mul_rpow (by norm_num) (by linarith)
    rw [hsplit2] at h2
    have hsplit3 : (2 * (d:ℝ))^(ε/4) = (2:ℝ)^(ε/4) * (d:ℝ)^(ε/4) :=
      Real.mul_rpow (by norm_num) hd0
    have hdadd : (d:ℝ)^(ε/4 + ε/8) = (d:ℝ)^(ε/4) * (d:ℝ)^(ε/8) := Real.rpow_add hdpos _ _
    have hexp : ε/4 + ε/8 = 3 * ε / 8 := by ring
    have hcore : Cd * (2 * (d:ℝ))^(ε/4) * (Real.log (8 * (d:ℝ))) ^ kd
        ≤ A₂ * (d:ℝ)^(3*ε/8) := by
      rw [hsplit3, hA₂]
      calc Cd * ((2:ℝ)^(ε/4) * (d:ℝ)^(ε/4)) * (Real.log (8 * (d:ℝ))) ^ kd
          = Cd * (2:ℝ)^(ε/4) * (d:ℝ)^(ε/4) * (Real.log (8 * (d:ℝ))) ^ kd := by ring
        _ ≤ Cd * (2:ℝ)^(ε/4) * (d:ℝ)^(ε/4)
              * (((kd + 1) / (ε/8)) ^ kd * ((8:ℝ)^(ε/8) * (d:ℝ)^(ε/8))) := by
            apply mul_le_mul_of_nonneg_left h2
            positivity
        _ = (Cd * (2:ℝ)^(ε/4) * ((kd + 1) / (ε/8)) ^ kd * (8:ℝ)^(ε/8))
              * ((d:ℝ)^(ε/4) * (d:ℝ)^(ε/8)) := by ring
        _ = (Cd * (2:ℝ)^(ε/4) * ((kd + 1) / (ε/8)) ^ kd * (8:ℝ)^(ε/8))
              * (d:ℝ)^(ε/4 + ε/8) := by rw [← hdadd]
        _ = (Cd * (2:ℝ)^(ε/4) * ((kd + 1) / (ε/8)) ^ kd * (8:ℝ)^(ε/8))
              * (d:ℝ)^(3*ε/8) := by rw [hexp]
    exact hcore.trans (mul_le_mul_of_nonneg_right hAle2 (by positivity))

end Work.FIArea6Hecke.R
