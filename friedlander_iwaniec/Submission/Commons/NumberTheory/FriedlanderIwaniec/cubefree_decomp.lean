import Submission.Commons.NumberTheory.FriedlanderIwaniec.cubefree_eq_squarefree_mul_sq

namespace Commons.NumberTheory.FriedlanderIwaniec

set_option linter.unusedVariables false

/-- **Cubefree decomposition.**  A cubefree `d` (no prime cube divides it) which is
not divisible by `4` is of the form `d = d₁ d₂²` with `d₁`, `d₂` squarefree and coprime.
(Proof: take `d₂` to be the product of the primes with `d.factorization p = 2` and `d₁`
the product of those with `d.factorization p = 1`; compare `Nat.factorization`s.) -/
theorem cubefree_decomp {d : ℕ} (hd : 0 < d)
    (hc : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d) (h4 : ¬ 4 ∣ d) :
    ∃ d₁ d₂ : ℕ, Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ d₁ * d₂ ^ 2 = d := by
  obtain ⟨d₁, d₂, h1, h2, h3, h4'⟩ := cubefree_eq_squarefree_mul_sq hd hc
  exact ⟨d₁, d₂, h1, h2, h3, h4'.symm⟩

end Commons.NumberTheory.FriedlanderIwaniec
