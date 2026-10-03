import Mathlib
import Submission.Work.FIArea7.MSmoothDefs

set_option linter.unusedVariables false

namespace Work.FIArea7

open Finset

noncomputable section

/-- Pointwise form: the `e`-th power of the prime weight `xp p` is the inverse
fourth root of `p ^ e`. -/
lemma xp_pow_eq_inv_rpow (p e : ℕ) :
    (xp p) ^ e = (((p : ℝ) ^ e : ℝ) ^ ((1 : ℝ) / 4))⁻¹ := by
  rw [xp, inv_pow]
  congr 1
  rw [← Real.rpow_mul_natCast (show (0 : ℝ) ≤ (p : ℝ) by positivity),
    mul_comm ((1 : ℝ) / 4) (e : ℝ), Real.rpow_natCast_mul (show (0 : ℝ) ≤ (p : ℝ) by positivity)]

/-- The product of the prime weights `xp p` raised to the multiplicities `v_p k`,
over the primes of `m`, equals `k^{-1/4}` whenever every prime of `k` divides `m`. -/
lemma xp_inv_eq_prod (m k : ℕ) (hm : 1 ≤ m) (hk1 : 1 ≤ k) (hsub : k.primeFactors ⊆ m.primeFactors) :
    ((k : ℝ) ^ ((1 : ℝ) / 4))⁻¹ = ∏ p ∈ m.primeFactors, (xp p) ^ (k.factorization p) := by
  have hk0 : k ≠ 0 := by omega
  -- `∏_{p | m} p^{v_p k} = k`
  have hnat : (∏ p ∈ m.primeFactors, p ^ (k.factorization p)) = k :=
    (Finset.prod_subset hsub (f := fun p => p ^ (k.factorization p))
        (fun p _ hpk => by
          rw [Nat.factorization_eq_zero_of_not_dvd (fun hd =>
            hpk (Nat.mem_primeFactors.mpr
              ⟨Nat.prime_of_mem_primeFactors (by assumption), hd, hk0⟩)), pow_zero])).symm.trans
      (Nat.prod_primeFactors_pow_factorization hk0).symm
  have hcast : (∏ p ∈ m.primeFactors, ((p : ℝ) ^ (k.factorization p))) = (k : ℝ) := by
    have h2 : (∏ p ∈ m.primeFactors, ((p : ℝ) ^ (k.factorization p)))
        = ((∏ p ∈ m.primeFactors, p ^ (k.factorization p) : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      exact Finset.prod_congr rfl (fun p _ => by push_cast; ring)
    rw [h2, hnat]
  rw [Finset.prod_congr rfl (fun p _ => xp_pow_eq_inv_rpow p (k.factorization p))]
  rw [Finset.prod_inv_distrib (fun p : ℕ => (((p : ℝ) ^ (k.factorization p)) ^ ((1 : ℝ) / 4)))]
  rw [Real.finsetProd_rpow m.primeFactors (fun p : ℕ => ((p : ℝ) ^ (k.factorization p)))
    (fun p _ => pow_nonneg (Nat.cast_nonneg p) _) ((1 : ℝ) / 4), hcast]

end

end Work.FIArea7
