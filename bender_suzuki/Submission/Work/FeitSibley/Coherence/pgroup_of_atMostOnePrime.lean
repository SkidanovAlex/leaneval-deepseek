import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.exists_prime_isPGroup_of_atMostOnePrime`

A nontrivial finite group whose order is divisible by at most one prime is a `p`-group.  This is
the elementary reduction used to reach the last case of
`Work.FeitSibley.Coherence.coherent_scriptS`: Peterfalvi II, Appendice XII assumes `Q₁` to be a
non-abelian `p`-group with `p` odd, which for the `FSData` of the area follows from the
hypotheses "`|Q₁|` is divisible by at most one prime" and "`Q₁` is not a `2`-group".
-/

namespace Work.FeitSibley.Coherence

/-- A nontrivial finite group whose order is divisible by at most one prime is a `p`-group for
that (unique) prime. -/
theorem exists_prime_isPGroup_of_atMostOnePrime {G : Type} [Group G] [Fintype G]
    (A : Subgroup G) (hA : A ≠ ⊥) (hnot2 : ¬ IsPGroup 2 A)
    (h2 : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.card A ∧ q ∣ Nat.card A) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p A := by
  have hcard : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hne1 : Nat.card A ≠ 1 := fun h1 => hA (Subgroup.card_eq_one.mp h1)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne1
  have hpg : IsPGroup p A := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    rw [IsPGroup.iff_card]
    exact ⟨(Nat.card A).primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd hcard fun {d} hd hddvd => by
        by_contra hdp
        exact h2 ⟨d, p, hd, hp, hdp, hddvd, hpdvd⟩⟩
  refine ⟨p, hp, ?_, hpg⟩
  intro hp2
  exact hnot2 (hp2 ▸ hpg)

end Work.FeitSibley.Coherence
