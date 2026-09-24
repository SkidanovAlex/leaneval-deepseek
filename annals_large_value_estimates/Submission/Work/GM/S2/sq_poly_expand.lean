import Mathlib

namespace Work.GM.S2

/-- Squaring a Dirichlet polynomial with coefficients `a`, truncated at `K`:
the product of two copies of `∑_{m ≤ K} a_m m^{it}` is reindexed by the value
`n = m₁ m₂ ∈ [1, K²]` of the product and then, for each `n`, by the divisor
`m₁ = m` of `n` with complementary factor `n / m ≤ K`. -/
theorem sq_poly_expand (K : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ m ∈ Finset.Icc 1 K, a m * (m : ℂ) ^ (Complex.I * ((t : ℝ) : ℂ))) ^ 2
      = ∑ n ∈ Finset.Icc 1 (K * K),
          (∑ m ∈ (Finset.Icc 1 K).filter (fun m => m ∣ n ∧ n / m ≤ K), a m * a (n / m))
            * (n : ℂ) ^ (Complex.I * ((t : ℝ) : ℂ)) := by
  set z : ℂ := Complex.I * ((t : ℝ) : ℂ) with hz
  have key : ∀ m k : ℕ, (m : ℂ) ^ z * (k : ℂ) ^ z = ((m * k : ℕ) : ℂ) ^ z := by
    intro m k
    rw [← Complex.natCast_mul_natCast_cpow, Nat.cast_mul]
  have hL : (∑ m ∈ Finset.Icc 1 K, a m * (m : ℂ) ^ z) ^ 2
      = ∑ p ∈ (Finset.Icc 1 K).product (Finset.Icc 1 K),
          (a p.1 * (p.1 : ℂ) ^ z) * (a p.2 * (p.2 : ℂ) ^ z) := by
    rw [pow_two, Finset.sum_mul_sum]
    exact (Finset.sum_product (Finset.Icc 1 K) (Finset.Icc 1 K)
      (fun p : ℕ × ℕ => (a p.1 * (p.1 : ℂ) ^ z) * (a p.2 * (p.2 : ℂ) ^ z))).symm
  have hR : (∑ n ∈ Finset.Icc 1 (K * K),
          (∑ m ∈ (Finset.Icc 1 K).filter (fun m => m ∣ n ∧ n / m ≤ K), a m * a (n / m))
            * (n : ℂ) ^ z)
      = ∑ q ∈ ((Finset.Icc 1 (K * K)).product (Finset.Icc 1 K)).filter
            (fun q => q.2 ∣ q.1 ∧ q.1 / q.2 ≤ K),
          (a q.2 * a (q.1 / q.2)) * (q.1 : ℂ) ^ z := by
    conv_lhs =>
      simp only [Finset.sum_mul, Finset.sum_filter, ite_mul, zero_mul]
      rw [← Finset.sum_product (Finset.Icc 1 (K * K)) (Finset.Icc 1 K)
        (fun q : ℕ × ℕ => if q.2 ∣ q.1 ∧ q.1 / q.2 ≤ K
          then (a q.2 * a (q.1 / q.2)) * (q.1 : ℂ) ^ z else 0)]
    exact (Finset.sum_filter (fun q : ℕ × ℕ => q.2 ∣ q.1 ∧ q.1 / q.2 ≤ K)
      (fun q : ℕ × ℕ => (a q.2 * a (q.1 / q.2)) * (q.1 : ℂ) ^ z)).symm
  rw [hL, hR]
  refine Finset.sum_bij (fun p _ => (p.1 * p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨m, k⟩ := p
    have hp' := Finset.mem_product.mp hp
    obtain ⟨hm1, hmK⟩ := Finset.mem_Icc.mp hp'.1
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hp'.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,
      Finset.mem_Icc.mpr ⟨hm1, hmK⟩⟩, ?_, ?_⟩
    · simpa using Nat.mul_le_mul hm1 hk1
    · exact Nat.mul_le_mul hmK hkK
    · exact ⟨k, rfl⟩
    · rw [Nat.mul_div_cancel_left k hm1]
      exact hkK
  · intro p₁ hp₁ p₂ hp₂ h
    obtain ⟨m₁, k₁⟩ := p₁
    obtain ⟨m₂, k₂⟩ := p₂
    have h1 : m₁ * k₁ = m₂ * k₂ := congrArg Prod.fst h
    have h2 : m₁ = m₂ := congrArg Prod.snd h
    have hm2 : 0 < m₂ := (Finset.mem_Icc.mp (Finset.mem_product.mp hp₂).1).1
    have hk : k₁ = k₂ := by
      rw [h2] at h1
      exact Nat.mul_left_cancel hm2 h1
    exact Prod.ext h2 hk
  · intro b hb
    obtain ⟨n, m⟩ := b
    have hb' := Finset.mem_filter.mp hb
    obtain ⟨hn1, hnKK⟩ := Finset.mem_Icc.mp (Finset.mem_product.mp hb'.1).1
    obtain ⟨hm1, hmK⟩ := Finset.mem_Icc.mp (Finset.mem_product.mp hb'.1).2
    obtain ⟨hdvd, hdivK⟩ := hb'.2
    refine ⟨(m, n / m), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hmK⟩,
      Finset.mem_Icc.mpr ⟨?_, hdivK⟩⟩, ?_⟩
    · rw [Nat.one_le_div_iff (by omega : 0 < m)]
      exact Nat.le_of_dvd (by omega : 0 < n) hdvd
    · exact Prod.ext (Nat.mul_div_cancel' hdvd) rfl
  · intro p hp
    obtain ⟨m, k⟩ := p
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
    dsimp only
    rw [Nat.mul_div_cancel_left k hm1, ← key m k]
    ring

end Work.GM.S2
