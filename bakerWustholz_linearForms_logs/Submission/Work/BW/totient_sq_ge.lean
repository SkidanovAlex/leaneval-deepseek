import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For a prime `p`, the single-prime factor `p * (1 - 1/p)^2 = (p-1)^2/p` is at least `1/2`,
with equality exactly when `p = 2`. -/
private lemma prime_factor_ge_half (p : ℕ) (hp : p.Prime) :
    (1 : ℝ) / 2 ≤ (p : ℝ) * (1 - (p : ℝ)⁻¹) ^ 2 := by
  rcases eq_or_ne p 2 with h | h
  · subst h; norm_num
  · have h3 : 3 ≤ p := by have := hp.two_le; omega
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    have hpR : (0 : ℝ) < (p : ℝ) := by linarith
    have hid : (p : ℝ) * (1 - (p : ℝ)⁻¹) ^ 2 = ((p : ℝ) - 1) ^ 2 / (p : ℝ) := by
      field_simp
    rw [hid, le_div_iff₀ hpR]
    nlinarith [hp3, sq_nonneg ((p : ℝ) - 3)]

/-- For a finset `s` of primes, `∏_{p ∈ s} p (1 - 1/p)^2 ≥ 1/2`: every factor is `≥ 1` except the
factor at `p = 2`, which is exactly `1/2`, and at most one element of `s` equals `2`. -/
private lemma prod_factor_ge_half (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (1 : ℝ) / 2 ≤ ∏ p ∈ s, ((p : ℝ) * (1 - (p : ℝ)⁻¹) ^ 2) := by
  have key : ∀ p ∈ s, p ≠ 2 → (1 : ℝ) ≤ (p : ℝ) * (1 - (p : ℝ)⁻¹) ^ 2 := by
    intro p hp hpne
    have hpp : p.Prime := hs p hp
    have h3 : 3 ≤ p := by have := hpp.two_le; omega
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    have hpR : (0 : ℝ) < (p : ℝ) := by linarith
    have hid : (p : ℝ) * (1 - (p : ℝ)⁻¹) ^ 2 = ((p : ℝ) - 1) ^ 2 / (p : ℝ) := by
      field_simp
    rw [hid, le_div_iff₀ hpR]
    nlinarith [hp3, sq_nonneg ((p : ℝ) - 3)]
  by_cases h2 : 2 ∈ s
  · rw [← Finset.mul_prod_erase s (fun p => (p : ℝ) * (1 - (p : ℝ)⁻¹) ^ 2) h2]
    have hf2 : (((2 : ℕ) : ℝ) * (1 - (((2 : ℕ) : ℝ))⁻¹) ^ 2) = (1 : ℝ) / 2 := by norm_num
    rw [hf2]
    have hone : (1 : ℝ) ≤ ∏ p ∈ s.erase 2, ((p : ℝ) * (1 - (p : ℝ)⁻¹) ^ 2) := by
      apply Finset.one_le_prod₀
      intro p hp
      exact key p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
    nlinarith [hone]
  · have hone : (1 : ℝ) ≤ ∏ p ∈ s, ((p : ℝ) * (1 - (p : ℝ)⁻¹) ^ 2) := by
      apply Finset.one_le_prod₀
      intro p hp
      exact key p hp (by rintro rfl; exact h2 hp)
    linarith

/-- The sharp elementary lower bound for Euler's totient: `φ(n) ≥ √(n/2)`, in squared form
`n ≤ 2 φ(n)²`. Equality holds at `n = 2`. -/
theorem totient_sq_ge (n : ℕ) (hn : 0 < n) : (n : ℝ) ≤ 2 * (Nat.totient n : ℝ) ^ 2 := by
  -- Euler's product formula, pushed from ℚ to ℝ.
  have hφ : (Nat.totient n : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := Nat.totient_eq_mul_prod_factors n
    have h' := congrArg (fun q : ℚ => (q : ℝ)) h
    simp only [Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one, Rat.cast_inv,
      Rat.cast_natCast] at h'
    exact h'
  set F : ℝ := ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) with hF
  have hrad_pos : 0 < (∏ p ∈ n.primeFactors, (p : ℝ)) :=
    Finset.prod_pos (fun p hp => by
      have := Nat.prime_of_mem_primeFactors hp
      exact_mod_cast this.pos)
  have hrad_le : (∏ p ∈ n.primeFactors, (p : ℝ)) ≤ (n : ℝ) := by
    have hle : (∏ p ∈ n.primeFactors, p) ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
    calc (∏ p ∈ n.primeFactors, (p : ℝ)) = ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by
          rw [Nat.cast_prod]
      _ ≤ (n : ℝ) := by exact_mod_cast hle
  have hprod : (1 : ℝ) / 2 ≤ (∏ p ∈ n.primeFactors, (p : ℝ)) * F ^ 2 := by
    rw [hF, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact prod_factor_ge_half n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkey : (1 : ℝ) / 2 ≤ (n : ℝ) * F ^ 2 := by
    have hdiv : 1 ≤ (n : ℝ) / (∏ p ∈ n.primeFactors, (p : ℝ)) :=
      (one_le_div hrad_pos).mpr hrad_le
    have hC : 0 ≤ (∏ p ∈ n.primeFactors, (p : ℝ)) * F ^ 2 :=
      mul_nonneg (le_of_lt hrad_pos) (sq_nonneg F)
    have hstep : (∏ p ∈ n.primeFactors, (p : ℝ)) * F ^ 2
        ≤ ((n : ℝ) / (∏ p ∈ n.primeFactors, (p : ℝ)))
            * ((∏ p ∈ n.primeFactors, (p : ℝ)) * F ^ 2) := by
      simpa using mul_le_mul_of_nonneg_right hdiv hC
    have hstep2 : ((n : ℝ) / (∏ p ∈ n.primeFactors, (p : ℝ)))
          * ((∏ p ∈ n.primeFactors, (p : ℝ)) * F ^ 2) = (n : ℝ) * F ^ 2 := by
      rw [← mul_assoc, div_mul_cancel₀ (n : ℝ) hrad_pos.ne']
    calc (1 : ℝ) / 2 ≤ (∏ p ∈ n.primeFactors, (p : ℝ)) * F ^ 2 := hprod
      _ ≤ ((n : ℝ) / (∏ p ∈ n.primeFactors, (p : ℝ)))
            * ((∏ p ∈ n.primeFactors, (p : ℝ)) * F ^ 2) := hstep
      _ = (n : ℝ) * F ^ 2 := hstep2
  rw [hφ]
  have h1 : (1 : ℝ) ≤ 2 * ((n : ℝ) * F ^ 2) := by linarith
  have h2 : (n : ℝ) ≤ (n : ℝ) * (2 * ((n : ℝ) * F ^ 2)) := by
    have := mul_le_mul_of_nonneg_left h1 (le_of_lt hnR)
    simpa using this
  calc (n : ℝ) ≤ (n : ℝ) * (2 * ((n : ℝ) * F ^ 2)) := h2
    _ = 2 * ((n : ℝ) * F) ^ 2 := by ring

end Work.BW
