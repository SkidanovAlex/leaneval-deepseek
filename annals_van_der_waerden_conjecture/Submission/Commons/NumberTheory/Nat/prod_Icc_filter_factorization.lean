import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace Commons.NumberTheory.Nat

theorem prod_Icc_filter_factorization (n D : ℕ) :
    (∏ j ∈ Finset.Icc 1 (n - 1),
        ∏ p ∈ (Nat.primeFactors D).filter (fun p => n < p ∧ j ≤ D.factorization p), p)
      = ∏ p ∈ (Nat.primeFactors D).filter (fun p => n < p),
          p ^ min (D.factorization p) (n - 1) := by
  have step1 : (∏ j ∈ Finset.Icc 1 (n - 1),
        ∏ p ∈ (Nat.primeFactors D).filter (fun p => n < p ∧ j ≤ D.factorization p), p)
      = ∏ j ∈ Finset.Icc 1 (n - 1),
          ∏ p ∈ (Nat.primeFactors D).filter (fun p => n < p),
            (if j ≤ D.factorization p then p else 1) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [← Finset.filter_filter (p := fun p => n < p) (q := fun p => j ≤ D.factorization p)]
    rw [Finset.prod_filter]
  rw [step1, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Finset.prod_filter, Finset.prod_const]
  congr 1
  have h : (Finset.Icc 1 (n-1)).filter (fun j => j ≤ D.factorization p)
      = Finset.Icc 1 (min (D.factorization p) (n-1)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [h, Nat.card_Icc]
  omega

end Commons.NumberTheory.Nat