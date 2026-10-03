import Mathlib
import Submission.Work.Peluse.Ulower.ss_defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- **Numeric core of `ss_conversion`.**  If `δ ≤ 1`, `c ≤ ρ`, `D ≤ Ns ≤ 2M`, then the "dual
scale ratio" `(Ns/D)·(δ ρ D/Ns)^{-K₁}` raised to the power `K₂` is bounded by
`2^{K₂(1+K₁)}·c^{-K₁K₂}·((M/D)δ^{-1})^{K₂(1+K₁)}`. -/
private lemma ss_vd_pow_le {K₁ K₂ : ℕ} {c δ ρ : ℝ} {D Ns M : ℕ}
    (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hcρ : c ≤ ρ)
    (hD : 1 ≤ D) (hNs : 1 ≤ Ns) (hDNs : D ≤ Ns) (hNsM : Ns ≤ 2 * M) :
    (((Ns : ℝ) / (D : ℝ)) * ((δ * ρ * (D : ℝ) / (Ns : ℝ)) ^ K₁)⁻¹) ^ K₂ ≤
      2 ^ (K₂ * (1 + K₁)) * (c⁻¹) ^ (K₁ * K₂) * (((M : ℝ) / (D : ℝ)) * δ⁻¹) ^ (K₂ * (1 + K₁)) := by
  have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hNs0 : (0:ℝ) < (Ns:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNs)
  have hρ0 : 0 < ρ := lt_of_lt_of_le hc hcρ
  have hδinv1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  -- (0) the exact identity `vd = (Ns/D)^{K₁+1}·(δρ)^{-K₁}`
  have hvd : ((Ns:ℝ)/(D:ℝ)) * ((δ * ρ * (D:ℝ) / (Ns:ℝ))^K₁)⁻¹
      = ((Ns:ℝ)/(D:ℝ))^(K₁+1) * ((δ*ρ)⁻¹)^K₁ := by
    have h1 : ((δ * ρ * (D:ℝ) / (Ns:ℝ))^K₁)⁻¹
        = ((δ*ρ)⁻¹ * ((Ns:ℝ)/(D:ℝ)))^K₁ := by
      rw [mul_div_assoc, ← inv_pow, mul_inv, mul_inv, inv_div]
    rw [h1, mul_pow]
    rw [pow_add, pow_one]
    ring
  -- (1) the first factor
  have hA : ((Ns:ℝ)/(D:ℝ))^(K₁+1) ≤ 2^(K₁+1) * ((M:ℝ)/(D:ℝ))^(K₁+1) := by
    have hle : (Ns:ℝ)/(D:ℝ) ≤ 2 * ((M:ℝ)/(D:ℝ)) := by
      have h : (Ns:ℝ)/(D:ℝ) ≤ ((2*M : ℕ) : ℝ)/(D:ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hNsM) (le_of_lt hD0)
      simpa [Nat.cast_mul, mul_div_assoc] using h
    calc ((Ns:ℝ)/(D:ℝ))^(K₁+1) ≤ (2 * ((M:ℝ)/(D:ℝ)))^(K₁+1) :=
          pow_le_pow_left₀ (by positivity) hle (K₁+1)
      _ = 2^(K₁+1) * ((M:ℝ)/(D:ℝ))^(K₁+1) := by rw [mul_pow]
  -- (2) the second factor
  have hB : ((δ*ρ)⁻¹)^K₁ ≤ (δ⁻¹)^K₁ * (c⁻¹)^K₁ := by
    have h2a : ρ⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hρ0 hc).mpr hcρ
    calc ((δ*ρ)⁻¹)^K₁ = (δ⁻¹ * ρ⁻¹)^K₁ := by rw [mul_inv]
      _ ≤ (δ⁻¹ * c⁻¹)^K₁ :=
          pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_left h2a (le_of_lt (inv_pos.mpr hδ0))) K₁
      _ = (δ⁻¹)^K₁ * (c⁻¹)^K₁ := by rw [mul_pow]
  -- (3) combine
  have hvd_le : ((Ns:ℝ)/(D:ℝ)) * ((δ * ρ * (D:ℝ) / (Ns:ℝ))^K₁)⁻¹
      ≤ 2^(K₁+1) * ((M:ℝ)/(D:ℝ))^(K₁+1) * ((δ⁻¹)^K₁ * (c⁻¹)^K₁) := by
    rw [hvd]
    calc ((Ns:ℝ)/(D:ℝ))^(K₁+1) * ((δ*ρ)⁻¹)^K₁
        ≤ (2^(K₁+1) * ((M:ℝ)/(D:ℝ))^(K₁+1)) * ((δ⁻¹)^K₁ * (c⁻¹)^K₁) :=
          mul_le_mul hA hB (by positivity) (by positivity)
      _ = 2^(K₁+1) * ((M:ℝ)/(D:ℝ))^(K₁+1) * ((δ⁻¹)^K₁ * (c⁻¹)^K₁) := by ring
  -- (4) raise to the power `K₂`
  have hpow : (((Ns:ℝ)/(D:ℝ)) * ((δ * ρ * (D:ℝ) / (Ns:ℝ))^K₁)⁻¹)^K₂
      ≤ (2^(K₁+1) * ((M:ℝ)/(D:ℝ))^(K₁+1) * ((δ⁻¹)^K₁ * (c⁻¹)^K₁))^K₂ :=
    pow_le_pow_left₀ (by positivity) hvd_le K₂
  -- (5) expand the raised bound
  have hexp : (2^(K₁+1) * ((M:ℝ)/(D:ℝ))^(K₁+1) * ((δ⁻¹)^K₁ * (c⁻¹)^K₁))^K₂
      = 2^((K₁+1)*K₂) * ((M:ℝ)/(D:ℝ))^((K₁+1)*K₂) *
          ((δ⁻¹)^(K₁*K₂) * (c⁻¹)^(K₁*K₂)) := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
  -- (6) compare exponents
  have hle : 2^((K₁+1)*K₂) * ((M:ℝ)/(D:ℝ))^((K₁+1)*K₂) *
              ((δ⁻¹)^(K₁*K₂) * (c⁻¹)^(K₁*K₂))
      ≤ 2^(K₂*(1+K₁)) * ((M:ℝ)/(D:ℝ))^(K₂*(1+K₁)) *
              ((δ⁻¹)^(K₂*(1+K₁)) * (c⁻¹)^(K₁*K₂)) := by
    have he : (K₁+1)*K₂ = K₂*(1+K₁) := by ring
    have hδ : (δ⁻¹)^(K₁*K₂) ≤ (δ⁻¹)^(K₂*(1+K₁)) := by
      apply pow_le_pow_right₀ hδinv1
      calc K₁*K₂ = K₂*K₁ := by ring
        _ ≤ K₂*(1+K₁) := Nat.mul_le_mul_left K₂ (by omega)
    rw [he]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right hδ (by positivity)
  -- (7) collect the last two factors
  have hfin : 2^(K₂*(1+K₁)) * ((M:ℝ)/(D:ℝ))^(K₂*(1+K₁)) *
              ((δ⁻¹)^(K₂*(1+K₁)) * (c⁻¹)^(K₁*K₂))
      = 2^(K₂*(1+K₁)) * (c⁻¹)^(K₁*K₂) * (((M:ℝ)/(D:ℝ))*δ⁻¹)^(K₂*(1+K₁)) := by
    have hm : (((M:ℝ)/(D:ℝ)) * δ⁻¹)^(K₂*(1+K₁))
        = ((M:ℝ)/(D:ℝ))^(K₂*(1+K₁)) * (δ⁻¹)^(K₂*(1+K₁)) := mul_pow _ _ _
    rw [hm]
    ring
  calc (((Ns:ℝ)/(D:ℝ)) * ((δ * ρ * (D:ℝ) / (Ns:ℝ))^K₁)⁻¹)^K₂
      ≤ (2^(K₁+1) * ((M:ℝ)/(D:ℝ))^(K₁+1) * ((δ⁻¹)^K₁ * (c⁻¹)^K₁))^K₂ := hpow
    _ = 2^((K₁+1)*K₂) * ((M:ℝ)/(D:ℝ))^((K₁+1)*K₂) *
          ((δ⁻¹)^(K₁*K₂) * (c⁻¹)^(K₁*K₂)) := hexp
    _ ≤ 2^(K₂*(1+K₁)) * ((M:ℝ)/(D:ℝ))^(K₂*(1+K₁)) *
          ((δ⁻¹)^(K₂*(1+K₁)) * (c⁻¹)^(K₁*K₂)) := hle
    _ = 2^(K₂*(1+K₁)) * (c⁻¹)^(K₁*K₂) * (((M:ℝ)/(D:ℝ))*δ⁻¹)^(K₂*(1+K₁)) := hfin
/-- **Conversion between the two scales.** -/
theorem ss_conversion {P : Polynomial ℤ} {C₂ K₁ K₂ : ℕ} {c : ℝ}
    (hC₂ : 1 ≤ C₂) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) (hc : 0 < c) :
    ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (Ns N N₀ D M : ℕ) (f₁ : ℤ → ℂ) (δ ρ A' : ℝ),
        1 ≤ M → 1 ≤ Ns → 1 ≤ N → 1 ≤ D → 1 ≤ A' →
        0 < δ → δ ≤ 1 → 0 < ρ → c ≤ ρ → ρ ≤ 1 →
        M ≤ Ns → Ns ≤ 2 * M → D ≤ M → D ≤ Ns → N₀ ≤ Ns →
        Work.Peluse.Ulower.DisplayAt P C₂ K₂ 1 Ns N Ns D f₁ ((δ * ρ * (D : ℝ) / (Ns : ℝ)) ^ K₁) →
        Work.Peluse.Ulower.DisplayAt P C K A' M N N₀ D f₁ δ := by
  set Ψ : ℝ := 2 ^ (K₂ * (1 + K₁)) * (c⁻¹) ^ (K₁ * K₂) with hΨdef
  set K : ℕ := K₂ * (1 + K₁) with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    calc (1:ℕ) ≤ 1 * (1 + K₁) := by rw [one_mul]; omega
      _ ≤ K₂ * (1 + K₁) := Nat.mul_le_mul_right _ hK₂
  set Bnd : ℝ := max 1 (max ((C₂:ℝ) * Ψ) ((C₂:ℝ) * Ψ^2)) with hBnddef
  set C : ℕ := ⌈Bnd⌉₊ with hCdef
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    have hle : (1:ℝ) ≤ (⌈Bnd⌉₊ : ℝ) := by
      refine le_trans ?_ (Nat.le_ceil Bnd)
      rw [hBnddef]
      exact le_max_left _ _
    exact_mod_cast hle
  have hCΨ : (C₂:ℝ) * Ψ ≤ (C:ℝ) := by
    rw [hCdef]
    calc (C₂:ℝ) * Ψ ≤ max ((C₂:ℝ)*Ψ) ((C₂:ℝ)*Ψ^2) := le_max_left _ _
      _ ≤ max 1 (max ((C₂:ℝ)*Ψ) ((C₂:ℝ)*Ψ^2)) := le_max_right _ _
      _ = Bnd := by rw [hBnddef]
      _ ≤ (⌈Bnd⌉₊ : ℝ) := Nat.le_ceil Bnd
  have hCΨ2 : (C₂:ℝ) * Ψ^2 ≤ (C:ℝ) := by
    rw [hCdef]
    calc (C₂:ℝ) * Ψ^2 ≤ max ((C₂:ℝ)*Ψ) ((C₂:ℝ)*Ψ^2) := le_max_right _ _
      _ ≤ max 1 (max ((C₂:ℝ)*Ψ) ((C₂:ℝ)*Ψ^2)) := le_max_right _ _
      _ = Bnd := by rw [hBnddef]
      _ ≤ (⌈Bnd⌉₊ : ℝ) := Nat.le_ceil Bnd
  refine ⟨C, K, hC1, hK1, ?_⟩
  intro Ns N N₀ D M f₁ δ ρ A' hM hNs hN hD hA'
    hδ0 hδ1 hρ0 hcρ hρ1 hMNs hNs2M hDM hDNs hN₀Ns hdisp
  obtain ⟨q, N', hq1, hq, hN'1, hN'N, h4, h5⟩ := hdisp
  set d1 : ℝ := (δ * ρ * (D:ℝ) / (Ns:ℝ))^K₁ with hd1def
  set ud : ℝ := d1 * ((D:ℝ)/(Ns:ℝ)) with huddef
  set vd : ℝ := ((Ns:ℝ)/(D:ℝ)) * d1⁻¹ with hvddef
  set β : ℝ := ((M:ℝ)/(D:ℝ)) * δ⁻¹ with hβdef
  set bt : ℝ := A' * β with hbtdef
  set ct : ℝ := δ * ((D:ℝ)/(M:ℝ)) with hctdef
  have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hNs0 : (0:ℝ) < (Ns:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNs)
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hA'0 : (0:ℝ) < A' := lt_of_lt_of_le one_pos hA'
  have hδinv1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  have hd1pos : 0 < d1 := by rw [hd1def]; positivity
  have hudpos : 0 < ud := by rw [huddef]; positivity
  have hvdpos : 0 < vd := by rw [hvddef]; positivity
  have hβpos : 0 < β := by rw [hβdef]; positivity
  have hbtpos : 0 < bt := by rw [hbtdef]; positivity
  have hctpos : 0 < ct := by rw [hctdef]; positivity
  have hΨpos : 0 < Ψ := by rw [hΨdef]; positivity
  have hAB : ((D:ℝ)/(Ns:ℝ)) * ((Ns:ℝ)/(D:ℝ)) = 1 := by
    rw [div_mul_div_comm]
    rw [show (D:ℝ) * (Ns:ℝ) = (Ns:ℝ) * (D:ℝ) by ring]
    exact mul_inv_cancel₀ (ne_of_gt (mul_pos hNs0 hD0))
  have huveq : ud * vd = 1 := by
    rw [huddef, hvddef]
    rw [show d1 * ((D:ℝ)/(Ns:ℝ)) * (((Ns:ℝ)/(D:ℝ)) * d1⁻¹)
        = (d1 * d1⁻¹) * (((D:ℝ)/(Ns:ℝ)) * ((Ns:ℝ)/(D:ℝ))) by ring]
    rw [mul_inv_cancel₀ (ne_of_gt hd1pos), one_mul, hAB]
  have hudinv : ud⁻¹ = vd := inv_eq_of_mul_eq_one_right huveq
  have hpow : (ud^K₂)⁻¹ = vd^K₂ := by rw [← inv_pow, hudinv]
  have hUn : ud^K₂ = d1^K₂ * ((D:ℝ)/(Ns:ℝ))^K₂ := by rw [huddef, mul_pow]
  have hVn : vd^K₂ = ((Ns:ℝ)/(D:ℝ))^K₂ * (d1⁻¹)^K₂ := by rw [hvddef, mul_pow]
  have hq' : (q:ℝ) ≤ (C₂:ℝ) * vd^K₂ := by
    rw [hVn]; simpa [one_pow, mul_assoc] using hq
  have h4ud : ud^K₂ * (N:ℝ) ≤ (C₂:ℝ) * vd^K₂ * (N':ℝ) := by
    rw [hUn, hVn]; simpa [one_pow, mul_assoc] using h4
  have h5ud : ud^K₂ * (Ns:ℝ) ≤ (C₂:ℝ) * vd^K₂ * progAvgSum N' (q:ℤ) f₁ := by
    rw [hUn, hVn]; simpa [one_pow, mul_assoc] using h5
  have h4' : (N:ℝ) ≤ (C₂:ℝ) * vd^(2*K₂) * (N':ℝ) := by
    have hstep : (N:ℝ) ≤ ((C₂:ℝ) * vd^K₂ * (N':ℝ)) / ud^K₂ := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact h4ud
    calc (N:ℝ) ≤ ((C₂:ℝ) * vd^K₂ * (N':ℝ)) / ud^K₂ := hstep
      _ = (C₂:ℝ) * vd^(2*K₂) * (N':ℝ) := by
          rw [div_eq_mul_inv, hpow]
          rw [two_mul, pow_add]
          ring
  have h5' : (Ns:ℝ) ≤ (C₂:ℝ) * vd^(2*K₂) * progAvgSum N' (q:ℤ) f₁ := by
    have hstep : (Ns:ℝ) ≤ ((C₂:ℝ) * vd^K₂ * progAvgSum N' (q:ℤ) f₁) / ud^K₂ := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact h5ud
    calc (Ns:ℝ) ≤ ((C₂:ℝ) * vd^K₂ * progAvgSum N' (q:ℤ) f₁) / ud^K₂ := hstep
      _ = (C₂:ℝ) * vd^(2*K₂) * progAvgSum N' (q:ℤ) f₁ := by
          rw [div_eq_mul_inv, hpow]
          rw [two_mul, pow_add]
          ring
  have hvdK : vd^K₂ ≤ Ψ * β^K := by
    have h := ss_vd_pow_le (K₁ := K₁) (K₂ := K₂) (c := c) (δ := δ) (ρ := ρ)
      (D := D) (Ns := Ns) (M := M) hc hδ0 hδ1 hcρ hD hNs hDNs hNs2M
    rw [hvddef, hd1def, hΨdef, hβdef, hKdef]
    exact h
  have hvd2K : vd^(2*K₂) ≤ Ψ^2 * β^(2*K) := by
    have h2 := pow_le_pow_left₀ (by positivity) hvdK 2
    have e1 : (vd^K₂)^2 = vd^(2*K₂) := by rw [← pow_mul, Nat.mul_comm K₂ 2]
    have e2 : (Ψ * β^K)^2 = Ψ^2 * β^(2*K) := by rw [mul_pow, ← pow_mul, Nat.mul_comm K 2]
    rw [e1, e2] at h2
    exact h2
  have hβbt : β ≤ bt := by
    rw [hbtdef]
    calc β = 1 * β := by rw [one_mul]
      _ ≤ A' * β := mul_le_mul_of_nonneg_right hA' (le_of_lt hβpos)
  have hbK : β^K ≤ bt^K := pow_le_pow_left₀ (le_of_lt hβpos) hβbt K
  have hctβ : ct * β = 1 := by
    rw [hctdef, hβdef]
    rw [show δ * ((D:ℝ)/(M:ℝ)) * (((M:ℝ)/(D:ℝ)) * δ⁻¹)
        = (δ * δ⁻¹) * (((D:ℝ)/(M:ℝ)) * ((M:ℝ)/(D:ℝ))) by ring]
    rw [mul_inv_cancel₀ (ne_of_gt hδ0), one_mul]
    rw [div_mul_div_comm]
    rw [show (D:ℝ) * (M:ℝ) = (M:ℝ) * (D:ℝ) by ring]
    exact mul_inv_cancel₀ (ne_of_gt (mul_pos hM0 hD0))
  have hctβK : ct^K * β^K = 1 := by rw [← mul_pow, hctβ, one_pow]
  have hctβ2K : ct^K * β^(2*K) = β^K := by
    rw [two_mul, pow_add, ← mul_assoc, hctβK, one_mul]
  have hbtA : (C:ℝ) * A' ^ K * ((M:ℝ)/(D:ℝ)) ^ K * (δ⁻¹) ^ K = (C:ℝ) * bt^K := by
    rw [hbtdef, hβdef]
    have e : (A' * (((M:ℝ)/(D:ℝ)) * δ⁻¹))^K = A'^K * (((M:ℝ)/(D:ℝ))^K * (δ⁻¹)^K) := by
      rw [mul_pow]
      have e2 : (((M:ℝ)/(D:ℝ)) * δ⁻¹)^K = ((M:ℝ)/(D:ℝ))^K * (δ⁻¹)^K := mul_pow _ _ _
      rw [e2]
    rw [e]
    ring
  have hctB : δ^K * ((D:ℝ)/(M:ℝ))^K * (N:ℝ) = ct^K * (N:ℝ) := by
    rw [hctdef]
    have e : (δ * ((D:ℝ)/(M:ℝ)))^K = δ^K * ((D:ℝ)/(M:ℝ))^K := mul_pow _ _ _
    rw [e]
  have hctC : δ^K * ((D:ℝ)/(M:ℝ))^K * (N₀:ℝ) = ct^K * (N₀:ℝ) := by
    rw [hctdef]
    have e : (δ * ((D:ℝ)/(M:ℝ)))^K = δ^K * ((D:ℝ)/(M:ℝ))^K := mul_pow _ _ _
    rw [e]
  have hps : (0:ℝ) ≤ progAvgSum N' (q:ℤ) f₁ := by rw [progAvgSum]; positivity
  have hN₀' : (N₀:ℝ) ≤ (Ns:ℝ) := by exact_mod_cast hN₀Ns
  refine ⟨q, N', hq1, ?_, hN'1, hN'N, ?_, ?_⟩
  · rw [hbtA]
    calc (q:ℝ) ≤ (C₂:ℝ) * vd^K₂ := hq'
      _ ≤ (C₂:ℝ) * (Ψ * β^K) := mul_le_mul_of_nonneg_left hvdK (by positivity)
      _ = ((C₂:ℝ) * Ψ) * β^K := by ring
      _ ≤ (C:ℝ) * β^K := mul_le_mul_of_nonneg_right hCΨ (by positivity)
      _ ≤ (C:ℝ) * bt^K := mul_le_mul_of_nonneg_left hbK (by positivity)
  · rw [hctB, hbtA]
    calc ct^K * (N:ℝ) ≤ ct^K * ((C₂:ℝ) * vd^(2*K₂) * (N':ℝ)) :=
          mul_le_mul_of_nonneg_left h4' (by positivity)
      _ ≤ ct^K * ((C₂:ℝ) * (Ψ^2 * β^(2*K)) * (N':ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hvd2K (by positivity)) (by positivity)
      _ = ((C₂:ℝ) * Ψ^2) * (ct^K * β^(2*K)) * (N':ℝ) := by ring
      _ = ((C₂:ℝ) * Ψ^2) * β^K * (N':ℝ) := by rw [hctβ2K]
      _ ≤ (C:ℝ) * β^K * (N':ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hCΨ2 (by positivity)
      _ ≤ (C:ℝ) * bt^K * (N':ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hbK (by positivity)
  · rw [hctC, hbtA]
    calc ct^K * (N₀:ℝ) ≤ ct^K * (Ns:ℝ) := mul_le_mul_of_nonneg_left hN₀' (by positivity)
      _ ≤ ct^K * ((C₂:ℝ) * vd^(2*K₂) * progAvgSum N' (q:ℤ) f₁) :=
          mul_le_mul_of_nonneg_left h5' (by positivity)
      _ ≤ ct^K * ((C₂:ℝ) * (Ψ^2 * β^(2*K)) * progAvgSum N' (q:ℤ) f₁) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hvd2K (by positivity)) hps
      _ = ((C₂:ℝ) * Ψ^2) * (ct^K * β^(2*K)) * progAvgSum N' (q:ℤ) f₁ := by ring
      _ = ((C₂:ℝ) * Ψ^2) * β^K * progAvgSum N' (q:ℤ) f₁ := by rw [hctβ2K]
      _ ≤ (C:ℝ) * β^K * progAvgSum N' (q:ℤ) f₁ := by
          apply mul_le_mul_of_nonneg_right _ hps
          exact mul_le_mul_of_nonneg_right hCΨ2 (by positivity)
      _ ≤ (C:ℝ) * bt^K * progAvgSum N' (q:ℤ) f₁ := by
          apply mul_le_mul_of_nonneg_right _ hps
          exact mul_le_mul_of_nonneg_left hbK (by positivity)


end

end Work.Peluse.Ulower
