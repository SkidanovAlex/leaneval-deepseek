import Submission.NK.Ramification.Tower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

/-- **The trivial case of the tower multiplicativity**: for an extension whose ramification
filtration is everywhere trivial (e.g. the trivial extension `M = ⊥` of `K` inside `L`), the
Herbrand function is the identity, so `φ_{L/K} = φ_{L/M} ∘ φ_{M/K}` reduces to `φ = φ`. -/
theorem herbrandRat_eq_id_of_forall_eq_bot {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L)
    (h : ∀ i : ℕ, NK.Ramification.ramificationSubgroup (K := K) A i = ⊥) (u : ℚ) :
    NK.Ramification.herbrandRat (K := K) A u = u := by
  have h1 : ∀ i : ℕ, NK.Ramification.lowerIndex (K := K) A i = 1 := by
    intro i
    rw [lowerIndex, h i]
    exact Nat.card_unique
  simp only [herbrandRat, h1, Nat.cast_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, div_one]
  ring

end NK.Ramification
