import Mathlib

namespace Work.FIArea7.KStarAP

lemma sqrt_prod_le_gcd_div (A : ℤ) (τ q M G m₁' m₂' : ℕ)
    (hτ : τ ≠ 0) (hq : q ≠ 0) (hM : 0 < M) (hMq : M ∣ q) (hGτ : G ∣ τ) (hGq : G ∣ q)
    (h1 : m₁' ∣ τ) (h2 : m₂' ∣ q)
    (hn1 : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ A → m₁'.factorization p = 0)
    (hn2 : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ A → m₂'.factorization p = 0)
    (hGA : ∀ p : ℕ, p.Prime → (p ∣ M ∨ p ∣ G) → (p : ℤ) ∣ A) :
    Real.sqrt ((m₁' : ℝ) * (m₂' : ℝ))
      ≤ ((Nat.gcd M G : ℝ) / (G : ℝ)) * Real.sqrt (((τ : ℝ) * (q : ℝ)) / (M : ℝ)) := by
  have hτpos : 0 < τ := Nat.pos_of_ne_zero hτ
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  have hGpos : 0 < G := Nat.pos_of_dvd_of_pos hGτ hτpos
  have hm1pos : 0 < m₁' := Nat.pos_of_dvd_of_pos h1 hτpos
  have hm2pos : 0 < m₂' := Nat.pos_of_dvd_of_pos h2 hqpos
  have hgpos : 0 < Nat.gcd M G := Nat.gcd_pos_of_pos_left G hM
  -- `m₁'` is coprime to `M` and to `G`
  have hc1M : Nat.Coprime m₁' M := by
    refine Nat.coprime_of_dvd fun p hp hpm hpn => ?_
    have hA : (p : ℤ) ∣ A := hGA p hp (Or.inl hpn)
    have h0 := hn1 p hp hA
    have hpos := hp.factorization_pos_of_dvd (ne_of_gt hm1pos) hpm
    omega
  have hc1G : Nat.Coprime m₁' G := by
    refine Nat.coprime_of_dvd fun p hp hpm hpn => ?_
    have hA : (p : ℤ) ∣ A := hGA p hp (Or.inr hpn)
    have h0 := hn1 p hp hA
    have hpos := hp.factorization_pos_of_dvd (ne_of_gt hm1pos) hpm
    omega
  have hc2M : Nat.Coprime m₂' M := by
    refine Nat.coprime_of_dvd fun p hp hpm hpn => ?_
    have hA : (p : ℤ) ∣ A := hGA p hp (Or.inl hpn)
    have h0 := hn2 p hp hA
    have hpos := hp.factorization_pos_of_dvd (ne_of_gt hm2pos) hpm
    omega
  have hc2G : Nat.Coprime m₂' G := by
    refine Nat.coprime_of_dvd fun p hp hpm hpn => ?_
    have hA : (p : ℤ) ∣ A := hGA p hp (Or.inr hpn)
    have h0 := hn2 p hp hA
    have hpos := hp.factorization_pos_of_dvd (ne_of_gt hm2pos) hpm
    omega
  have hcop_nvd : ∀ {m n : ℕ}, Nat.Coprime m n → ∀ p : ℕ, p.Prime → p ∣ m → ¬ p ∣ n :=
    fun h p hp hpm => hp.coprime_iff_not_dvd.mp (h.of_dvd_left hpm)
  have hc2MG : Nat.Coprime m₂' (M * G) := by
    refine Nat.coprime_of_dvd fun p hp hpm hpn => ?_
    rcases hp.dvd_mul.mp hpn with h | h
    · exact hcop_nvd hc2M p hp hpm h
    · exact hcop_nvd hc2G p hp hpm h
  have hL_dvd_MG : M.lcm G ∣ M * G := Nat.lcm_dvd ⟨G, rfl⟩ ⟨M, mul_comm M G⟩
  have hc2lcm : Nat.Coprime m₂' (M.lcm G) := hc2MG.of_dvd_right hL_dvd_MG
  have hL_dvd_q : M.lcm G ∣ q := Nat.lcm_dvd hMq hGq
  have hm2L_dvd : m₂' * (M.lcm G) ∣ q := hc2lcm.mul_dvd_of_dvd_of_dvd h2 hL_dvd_q
  have hm2L_le : m₂' * (M.lcm G) ≤ q := Nat.le_of_dvd hqpos hm2L_dvd
  have hm1G_dvd : m₁' * G ∣ τ := hc1G.mul_dvd_of_dvd_of_dvd h1 hGτ
  have hm1G_le : m₁' * G ≤ τ := Nat.le_of_dvd hτpos hm1G_dvd
  -- `m₂' * M * G ≤ q * gcd M G`
  have hkey : m₂' * M * G ≤ q * Nat.gcd M G := by
    have hMG : M * G = Nat.gcd M G * (M.lcm G) := (Nat.gcd_mul_lcm M G).symm
    have heq : m₂' * M * G = Nat.gcd M G * (m₂' * (M.lcm G)) := by
      calc m₂' * M * G = m₂' * (M * G) := by ring
        _ = m₂' * (Nat.gcd M G * (M.lcm G)) := by rw [hMG]
        _ = Nat.gcd M G * (m₂' * (M.lcm G)) := by ring
    rw [heq]
    calc Nat.gcd M G * (m₂' * M.lcm G) ≤ Nat.gcd M G * q := Nat.mul_le_mul_left _ hm2L_le
      _ = q * Nat.gcd M G := by ring
  have hmain : m₁' * m₂' * M * G ^ 2 ≤ τ * q * (Nat.gcd M G) ^ 2 := by
    have hgsq : Nat.gcd M G ≤ (Nat.gcd M G) ^ 2 := by
      have h1g : 1 ≤ Nat.gcd M G := hgpos
      have := Nat.mul_le_mul_left (Nat.gcd M G) h1g
      simpa [pow_two] using this
    calc m₁' * m₂' * M * G ^ 2 = (m₁' * G) * (m₂' * M * G) := by ring
      _ ≤ τ * (q * Nat.gcd M G) := Nat.mul_le_mul hm1G_le hkey
      _ = τ * q * Nat.gcd M G := by ring
      _ ≤ τ * q * (Nat.gcd M G) ^ 2 := Nat.mul_le_mul_left _ hgsq
  -- pass to ℝ
  have hGposR : (0:ℝ) < (G:ℝ) := by exact_mod_cast hGpos
  have hMposR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hMgR : (0:ℝ) < (M:ℝ) * (G:ℝ)^2 := by positivity
  have hb_nn : 0 ≤ ((τ:ℝ) * (q:ℝ)) / (M:ℝ) := by positivity
  have hR_nn : 0 ≤ ((Nat.gcd M G : ℝ) / (G:ℝ)) * Real.sqrt (((τ:ℝ) * (q:ℝ)) / (M:ℝ)) := by
    apply mul_nonneg
    · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hGposR)
    · exact Real.sqrt_nonneg _
  have hmainR : ((m₁' * m₂' * M * G^2 : ℕ) : ℝ)
      ≤ ((τ * q * (Nat.gcd M G)^2 : ℕ) : ℝ) := by
    exact_mod_cast hmain
  push_cast at hmainR
  rw [Real.sqrt_le_left hR_nn, mul_pow, Real.sq_sqrt hb_nn]
  have hEq : ((Nat.gcd M G : ℝ) / (G:ℝ))^2 * (((τ:ℝ) * (q:ℝ)) / (M:ℝ))
      = (Nat.gcd M G : ℝ)^2 * ((τ:ℝ) * (q:ℝ)) / ((M:ℝ) * (G:ℝ)^2) := by
    ring_nf
  rw [hEq, le_div_iff₀ hMgR]
  nlinarith [hmainR]

end Work.FIArea7.KStarAP
