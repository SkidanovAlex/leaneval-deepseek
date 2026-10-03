import Mathlib

namespace Work.Peluse.UlowerA

theorem pinLossU {σ K : ℕ} (hK : 1 ≤ K) (hσ : 1 ≤ σ) (d : ℕ)
    {γ δ B S D N Ns A : ℝ} {T : ℕ} {ε Λ C_S C' : ℝ}
    (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hγ0 : 0 < γ) (hγ9 : γ ≤ 9)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hC' : 0 < C')
    (hC_S : 1 ≤ C_S) (hNs : 1 ≤ Ns) (hA : 1 ≤ A) (hNd : Ns ≤ A * N ^ d)
    (hS : S + σ * D ≤ C_S * Ns)
    (hBnd : Real.sqrt (γ / 4) * B ≤ 2 * (S + σ * D) + 1)
    (hTle : (T : ℝ) ≤ 2 + 4 * Real.pi * (2 * B + 1) / Real.sqrt γ)
    (hε : ε = C' * (δ⁻¹) ^ K / N ^ d)
    (hΛ : Λ ≤ ((2 : ℝ) ^ (σ + 1) + 3) * 4 * ((C' * (δ⁻¹) ^ K + 2) * (C' * (δ⁻¹) ^ K + 1)) *
        ((Nat.floor (2 * ε * (T : ℝ)) : ℝ) + 1)) :
    δ ^ (3 * K) * Λ ≤
      (((2 : ℝ) ^ (σ + 1) + 3) * 4 * (C' + 2) ^ 2 *
        (2 * (C' * (18 + 48 * Real.pi * (2 * C_S * A + 1))) + 9)) / γ := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hspos : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ0
  have hsne : Real.sqrt γ ≠ 0 := ne_of_gt hspos
  have hsn : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg γ
  have hsle3 : Real.sqrt γ ≤ 3 := by
    have := Real.sqrt_le_sqrt hγ9
    rwa [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)] at this
  have hδKpos : 0 < δ^K := pow_pos hδ0 K
  have hδKne : δ^K ≠ 0 := ne_of_gt hδKpos
  have hδKle : δ^K ≤ 1 := pow_le_one₀ (le_of_lt hδ0) hδ1
  have hδ3Kpos : 0 < δ^(3*K) := pow_pos hδ0 _
  have hdKin : δ^K * (δ⁻¹)^K = 1 := by
    rw [inv_pow]
    exact mul_inv_cancel₀ hδKne
  have hNdpos : 0 < N^d := pow_pos (by linarith) d
  have hNd1 : 1 ≤ N^d := one_le_pow₀ hN
  have hεpos : 0 < ε := by rw [hε]; positivity
  -- (1) the product of the two `C'δ^{-K}+i` factors, after multiplying by δ^{2K}
  have hprod : δ^(2*K) * ((C'*(δ⁻¹)^K + 2)*(C'*(δ⁻¹)^K + 1)) ≤ (C'+2)^2 := by
    have hx : (δ⁻¹)^K = (δ^K)⁻¹ := inv_pow δ K
    rw [hx]
    have h2 : δ^(2*K) = δ^K * δ^K := by rw [two_mul, pow_add]
    rw [h2]
    have heq : δ^K * δ^K * ((C'*(δ^K)⁻¹+2)*(C'*(δ^K)⁻¹+1)) = (C'+2*δ^K)*(C'+δ^K) := by
      field_simp
    rw [heq]
    have h1 : C' + 2*δ^K ≤ C'+2 := by linarith only [hδKle]
    have h2' : C'+δ^K ≤ C'+2 := by linarith only [hδKle]
    have h3 : 0 ≤ C'+δ^K := by linarith only [hC', hδKpos]
    have h4 : 0 ≤ C'+2 := by linarith only [hC']
    calc (C'+2*δ^K)*(C'+δ^K) ≤ (C'+2)*(C'+2) := mul_le_mul h1 h2' h3 h4
      _ = (C'+2)^2 := by ring
  -- (2) δ^K * ε = C'/N^d
  have hεK : δ^K * ε = C'/N^d := by
    rw [hε]
    have he : δ^K * (C' * (δ⁻¹)^K / N^d) = C' * (δ^K * (δ⁻¹)^K) / N^d := by ring
    rw [he, hdKin]
    simp
  -- (3) the floor bound
  have hfl : (Nat.floor (2 * ε * (T:ℝ)) : ℝ) + 1 ≤ 2*ε*(T:ℝ) + 1 := by
    have h0 : 0 ≤ 2*ε*(T:ℝ) := by positivity
    have hle := Nat.floor_le h0
    linarith only [hle]
  have hmid : δ^K * ((Nat.floor (2 * ε * (T:ℝ)) : ℝ) + 1) ≤ 2*C'*(T:ℝ)/N^d + 1 := by
    have h1 : δ^K * ((Nat.floor (2 * ε * (T:ℝ)) : ℝ) + 1) ≤ 2*δ^K*ε*(T:ℝ) + δ^K := by
      have hh := mul_le_mul_of_nonneg_left hfl (le_of_lt hδKpos)
      have hh2 : δ^K * (2*ε*(T:ℝ) + 1) = 2*δ^K*ε*(T:ℝ) + δ^K := by ring
      linarith only [hh, hh2]
    have h2 : 2*δ^K*ε*(T:ℝ) + δ^K ≤ 2*C'*(T:ℝ)/N^d + 1 := by
      have he : 2*δ^K*ε*(T:ℝ) = 2*C'*(T:ℝ)/N^d := by
        rw [show 2*δ^K*ε*(T:ℝ) = 2*(δ^K*ε)*(T:ℝ) by ring, hεK]
        ring
      rw [he]
      linarith only [hδKle]
    linarith only [h1, h2]
  -- (4) the square-root bound
  have hB' : Real.sqrt γ*(2*B+1) ≤ 8*(S + σ*D) + 7 := by
    have hs4 : Real.sqrt (γ/4) = Real.sqrt γ / 2 := by
      rw [Real.sqrt_div (le_of_lt hγ0), show (4:ℝ) = 2^2 by norm_num,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [hs4] at hBnd
    nlinarith only [hBnd, hsle3, hsn]
  have hSD : 8*(S + σ*D) + 7 ≤ (8*C_S*A + 7)*N^d := by
    have hCSpos : 0 ≤ C_S := by linarith only [hC_S]
    have h1 : S + σ*D ≤ C_S*A*N^d := by
      have h2 := mul_le_mul_of_nonneg_left hNd hCSpos
      linarith only [hS, h2]
    nlinarith only [h1, hNd1]
  -- (5) the main numerical bound
  have hfinal : 2*C'*(T:ℝ)/N^d + 1 ≤ (2*(C'*(18+48*Real.pi*(2*C_S*A+1)))+9)/γ := by
    have htg : 2*(C'*(18+48*Real.pi*(2*C_S*A+1)))+9
        = 36*C' + 192*Real.pi*C'*C_S*A + 96*Real.pi*C' + 9 := by ring
    rw [le_div_iff₀ hγ0]
    have hb : 2*C'*(T:ℝ)*γ/N^d ≤ (4*C'*γ + 8*Real.pi*C'*(Real.sqrt γ*(2*B+1)))/N^d := by
      have hfac : 0 ≤ 2*C'*γ/N^d := by positivity
      have hstep := mul_le_mul_of_nonneg_left hTle hfac
      have hL : 2*C'*γ/N^d*(T:ℝ) = 2*C'*(T:ℝ)*γ/N^d := by ring
      have hR : 2*C'*γ/N^d*(2 + 4*Real.pi*(2*B+1)/Real.sqrt γ)
          = (4*C'*γ + 8*Real.pi*C'*(Real.sqrt γ*(2*B+1)))/N^d := by
        field_simp
        ring_nf
        rw [Real.sq_sqrt (le_of_lt hγ0)]
      rw [hL, hR] at hstep
      exact hstep
    have hc : (4*C'*γ + 8*Real.pi*C'*(Real.sqrt γ*(2*B+1)))/N^d
        ≤ 36*C' + 64*Real.pi*C'*C_S*A + 56*Real.pi*C' := by
      rw [div_le_iff₀ hNdpos]
      have h1 : 8*Real.pi*C'*(Real.sqrt γ*(2*B+1)) ≤ 8*Real.pi*C'*((8*C_S*A+7)*N^d) := by
        have hnn : 0 ≤ 8*Real.pi*C' := by positivity
        exact mul_le_mul_of_nonneg_left (le_trans hB' hSD) hnn
      have h3 : 8*Real.pi*C'*((8*C_S*A+7)*N^d)
          = (64*Real.pi*C'*C_S*A + 56*Real.pi*C')*N^d := by ring
      rw [h3] at h1
      have h2 : 4*C'*γ ≤ 36*C'*N^d := by
        have h2a : 4*C'*γ ≤ 36*C' := by nlinarith only [hγ9, hC']
        have h2b : 36*C' ≤ 36*C'*N^d := by nlinarith only [hNd1, hC']
        linarith only [h2a, h2b]
      linarith only [h1, h2]
    have hd : 36*C' + 64*Real.pi*C'*C_S*A + 56*Real.pi*C' + γ
        ≤ 2*(C'*(18+48*Real.pi*(2*C_S*A+1)))+9 := by
      rw [htg]
      have h1 : 64*Real.pi*C'*C_S*A ≤ 192*Real.pi*C'*C_S*A := by
        have hnn : 0 ≤ 128*Real.pi*C'*C_S*A := by positivity
        linarith only [hnn]
      have h2 : 56*Real.pi*C' ≤ 96*Real.pi*C' := by
        have hnn : 0 ≤ 40*Real.pi*C' := by positivity
        linarith only [hnn]
      linarith only [h1, h2, hγ9]
    have hexp : (2*C'*(T:ℝ)/N^d + 1)*γ = 2*C'*(T:ℝ)*γ/N^d + γ := by ring
    rw [hexp]
    linarith only [hb, hc, hd]
  -- (6) assembly
  have hA : 0 ≤ ((2:ℝ)^(σ+1)+3)*4 := by positivity
  have hRHSnn : 0 ≤ (C'+2)^2 := by positivity
  have hCn : 0 ≤ δ^K * ((Nat.floor (2 * ε * (T:ℝ)) : ℝ) + 1) := by positivity
  have h3K : δ^(3*K) = δ^(2*K) * δ^K := by
    rw [show 3*K = 2*K + K by ring, pow_add]
  calc δ^(3*K) * Λ
      ≤ δ^(3*K) * (((2:ℝ)^(σ+1)+3)*4 * ((C'*(δ⁻¹)^K + 2)*(C'*(δ⁻¹)^K+1)) *
          ((Nat.floor (2 * ε * (T:ℝ)) : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hΛ (le_of_lt hδ3Kpos)
    _ = ((2:ℝ)^(σ+1)+3)*4 * (δ^(2*K) * ((C'*(δ⁻¹)^K + 2)*(C'*(δ⁻¹)^K+1))) *
          (δ^K * ((Nat.floor (2 * ε * (T:ℝ)) : ℝ) + 1)) := by
        rw [h3K]; ring
    _ ≤ ((2:ℝ)^(σ+1)+3)*4 * (C'+2)^2 * ((2*(C'*(18+48*Real.pi*(2*C_S*A+1)))+9)/γ) := by
        have hmid' : δ^K * ((Nat.floor (2 * ε * (T:ℝ)) : ℝ) + 1)
            ≤ (2*(C'*(18+48*Real.pi*(2*C_S*A+1)))+9)/γ := le_trans hmid hfinal
        have hbc := mul_le_mul hprod hmid' hCn hRHSnn
        have hfin := mul_le_mul_of_nonneg_left hbc hA
        simpa only [mul_assoc] using hfin
    _ = (((2:ℝ)^(σ+1)+3)*4*(C'+2)^2*(2*(C'*(18+48*Real.pi*(2*C_S*A+1)))+9))/γ := by ring

end Work.Peluse.UlowerA
