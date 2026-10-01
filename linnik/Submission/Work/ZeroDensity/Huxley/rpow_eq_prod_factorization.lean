import Mathlib

namespace Work.ZeroDensity.Huxley

/-- `n^δ` as the product, over the prime factors of `n`, of `p^{δ·v_p(n)}`.
Proof idea: `n = ∏ p ∈ n.primeFactors, p ^ v_p(n)` (`Nat.prod_primeFactors_pow_factorization`), cast to ℝ
(`Nat.cast_prod`, `Nat.cast_pow`, `Real.rpow_natCast`), then `x^{v·δ} = (x^v)^δ` (`Real.rpow_mul`) and
distribute the `δ`-power over the product (`Real.finsetProd_rpow`). -/
lemma rpow_eq_prod_factorization {δ : ℝ} {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) ^ δ = ∏ x ∈ n.primeFactors, (x : ℝ) ^ ((n.factorization x : ℝ) * δ) := by
  have hcast : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    push_cast
    rfl
  rw [hcast, ← Real.finsetProd_rpow n.primeFactors (fun p => (p : ℝ) ^ n.factorization p)
        (fun p _ => by positivity) δ]
  apply Finset.prod_congr rfl
  intro p hp
  exact (Real.rpow_natCast_mul (Nat.cast_nonneg p) (n.factorization p) δ).symm

end Work.ZeroDensity.Huxley
