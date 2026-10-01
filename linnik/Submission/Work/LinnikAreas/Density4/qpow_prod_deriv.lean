import Mathlib

open scoped BigOperators

namespace Work.LinnikAreas.Density4

/-- The Euler-product value at `s = 1`, over the complex numbers:
`∏_{p | q} (1 - 1/p) = φ(q)/q`.  This is the complex form of
`Nat.totient_eq_mul_prod_factors`. -/
lemma prod_one_sub_inv_primeFactors (q : ℕ) [NeZero q] :
    ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) = (q.totient : ℂ) / (q : ℂ) := by
  have h := Nat.totient_eq_mul_prod_factors q
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have h2 : (∏ p ∈ q.primeFactors, (1 - (p : ℚ)⁻¹)) = (q.totient : ℚ) / (q : ℚ) := by
    rw [h, eq_div_iff hq]
    ring
  have h3 : ((∏ p ∈ q.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℂ)
      = (((q.totient : ℚ) / (q : ℚ) : ℚ) : ℂ) := by rw [h2]
  push_cast at h3
  exact h3

/-- The rearrangement of the logarithmic derivative of the Euler product at `s = 1`:
the derivative `∑_p (∏_{p' ≠ p} (1 - 1/p')) · (log p)/p` factors as
`(∏_{p} (1 - 1/p)) · ∑_p (log p)/(p - 1)`.  Uses `(1 - 1/p)·(log p)/(p-1) = (log p)/p`. -/
lemma sum_erase_mul_deriv (q : ℕ) [NeZero q] :
    (∑ p ∈ q.primeFactors,
        (∏ p' ∈ q.primeFactors.erase p, (1 - (p' : ℂ)⁻¹)) * ((p : ℂ)⁻¹ * (Real.log p : ℂ)))
      = (∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹))
        * (∑ p ∈ q.primeFactors, ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ)) := by
  have ha : ∀ p ∈ q.primeFactors,
      (p : ℂ)⁻¹ * (Real.log p : ℂ)
        = (1 - (p : ℂ)⁻¹) * ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hpp.ne_zero
    have hp1 : (p : ℂ) - 1 ≠ 0 := by
      intro h
      have h1 : (p : ℂ) = 1 := sub_eq_zero.mp h
      have : p = 1 := by exact_mod_cast h1
      exact hpp.ne_one this
    push_cast
    field_simp
  have key : ∀ p ∈ q.primeFactors,
      (∏ p' ∈ q.primeFactors.erase p, (1 - (p' : ℂ)⁻¹)) * ((p : ℂ)⁻¹ * (Real.log p : ℂ))
        = (∏ p' ∈ q.primeFactors, (1 - (p' : ℂ)⁻¹))
          * ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ) := by
    intro p hp
    rw [ha p hp, ← mul_assoc, Finset.prod_erase_mul _ _ hp]
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- The logarithmic derivative at `s = 1` of `q^s · ∏_{p | q}(1 - p^{-s})`:
the function is `q^s · φ(q)/q` at `s = 1` with logarithmic derivative
`log q + ∑_{p | q} log p/(p-1)`. -/
theorem qpow_prod_deriv (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    HasDerivAt
      (fun s : ℂ => (q : ℂ) ^ s * ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)))
      ((q.totient : ℂ) * ((Real.log q : ℂ)
        + ∑ p ∈ q.primeFactors, ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ)))
      1 := by
  -- derivative of `s ↦ q^s`
  have hA : HasDerivAt (fun s : ℂ => (q : ℂ) ^ s) ((Real.log q : ℂ) * (q : ℂ)) 1 := by
    have hslit : (q : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.natCast_mem_slitPlane]; exact NeZero.ne q
    have h1 : HasDerivAt (fun s : ℂ => (q : ℂ) ^ s)
        ((1 : ℂ) * (q : ℂ) ^ ((1 : ℂ) - 1) * 0 + (q : ℂ) ^ (1 : ℂ) * Complex.log (q : ℂ) * 1) 1 :=
      (hasDerivAt_const (1 : ℂ) (q : ℂ)).cpow (hasDerivAt_id (1 : ℂ)) hslit
    rw [show (1 : ℂ) * (q : ℂ) ^ ((1 : ℂ) - 1) * 0 + (q : ℂ) ^ (1 : ℂ) * Complex.log (q : ℂ) * 1
          = (Real.log q : ℂ) * (q : ℂ) by
      rw [show (1 : ℂ) - 1 = 0 by ring, Complex.cpow_zero, Complex.cpow_one,
        ← Complex.natCast_log (n := q)]
      ring] at h1
    exact h1
  -- derivative of each Euler factor `s ↦ 1 - p^{-s}`
  have hderiv_factor : ∀ p : ℕ, p.Prime →
      HasDerivAt (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) ((p : ℂ)⁻¹ * (Real.log p : ℂ)) 1 := by
    intro p hp
    have hslit : (p : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.natCast_mem_slitPlane]; exact hp.ne_zero
    have hg : HasDerivAt (fun s : ℂ => (p : ℂ) ^ (-s)) (-((p : ℂ)⁻¹ * (Real.log p : ℂ))) 1 := by
      have h1 : HasDerivAt (fun s : ℂ => (p : ℂ) ^ (-s))
          ((-1 : ℂ) * (p : ℂ) ^ ((-1 : ℂ) - 1) * 0
            + (p : ℂ) ^ (-1 : ℂ) * Complex.log (p : ℂ) * (-1)) 1 :=
        (hasDerivAt_const (1 : ℂ) (p : ℂ)).cpow ((hasDerivAt_id (1 : ℂ)).neg) hslit
      have h2 : ((-1 : ℂ) * (p : ℂ) ^ ((-1 : ℂ) - 1) * 0
            + (p : ℂ) ^ (-1 : ℂ) * Complex.log (p : ℂ) * (-1))
          = -((p : ℂ)⁻¹ * (Real.log p : ℂ)) := by
        rw [← Complex.natCast_log (n := p), Complex.cpow_neg_one]
        ring
      rwa [h2] at h1
    have h3 := hg.const_sub (1 : ℂ)
    simpa using h3
  -- derivative of the Euler product
  have hB : HasDerivAt (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)))
      (∑ p ∈ q.primeFactors, (∏ p' ∈ q.primeFactors.erase p, (1 - (p' : ℂ)⁻¹))
        * ((p : ℂ)⁻¹ * (Real.log p : ℂ))) 1 := by
    have h := HasDerivAt.finset_prod (u := q.primeFactors)
        (f := fun p => fun s : ℂ => 1 - (p : ℂ) ^ (-s))
        (f' := fun p => (p : ℂ)⁻¹ * (Real.log p : ℂ))
        (fun p hp => hderiv_factor p (Nat.prime_of_mem_primeFactors hp))
    have hf : (∏ i ∈ q.primeFactors, (fun s : ℂ => 1 - (i : ℂ) ^ (-s)))
        = (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) := by
      funext s; simp [Finset.prod_apply]
    rw [hf] at h
    simpa [Complex.cpow_neg_one, smul_eq_mul] using h
  have hmain := hA.mul hB
  -- evaluate the derivative
  have hval : ((Real.log q : ℂ) * (q : ℂ)) * ((q.totient : ℂ) / (q : ℂ))
      + (q : ℂ) * (((q.totient : ℂ) / (q : ℂ))
          * (∑ p ∈ q.primeFactors, ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ)))
      = (q.totient : ℂ) * ((Real.log q : ℂ)
          + ∑ p ∈ q.primeFactors, ((Real.log p / ((p : ℝ) - 1) : ℝ) : ℂ)) := by
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
    field_simp
  simp only [Complex.cpow_neg_one] at hmain
  rw [sum_erase_mul_deriv q, prod_one_sub_inv_primeFactors q, Complex.cpow_one] at hmain
  rw [hval] at hmain
  exact hmain

end Work.LinnikAreas.Density4
