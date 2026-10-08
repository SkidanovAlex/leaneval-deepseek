import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The order of a finite group acting freely divides the cardinality of the set

If a finite group `K` acts on a finite type `X` with no non-identity element fixing any
point (a *free* action), then `Nat.card K ∣ Nat.card X`.

This is the orbit-stabilizer theorem in its global form: a free action has all
stabilizers trivial, so every orbit is a free `K`-set and hence has cardinality `Nat.card K`;
`X` is the disjoint union of its orbits, so `Nat.card X` is the number of orbits times
`Nat.card K`.

We prove it here via **Burnside's lemma**
(`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`), which states
`∑ g, |Fix g| = #orbits * |K|`.  For a free action the only fixed points are those of the
identity, so the sum collapses to `|X|`, giving `|X| = #orbits * |K|`.
-/

set_option linter.style.haveILetI false

namespace Work.ThmF.Prove.S3

theorem card_dvd_card_of_free_action {K X : Type*} [Group K] [Finite K] [MulAction K X] [Finite X] (hfree : ∀ k : K, k ≠ 1 → ∀ x : X, k • x = x → False) : Nat.card K ∣ Nat.card X := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype X := Fintype.ofFinite X
  haveI : ∀ g : K, Fintype (MulAction.fixedBy X g) := fun g => Fintype.ofFinite _
  haveI : Fintype (Quotient (MulAction.orbitRel K X)) := Fintype.ofFinite _
  -- Burnside's lemma
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group K X
  -- The only element with a nonempty fixed-point set is the identity.
  have hsum : (∑ g : K, Fintype.card (MulAction.fixedBy X g)) = Fintype.card X := by
    rw [Finset.sum_eq_single (1 : K)]
    · simp
    · intro g _ hg
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun x => hfree g hg x.1 (MulAction.mem_fixedBy.mp x.2)⟩
    · intro h
      exact absurd (Finset.mem_univ (1 : K)) h
  rw [hsum] at hburn
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact ⟨_, hburn.trans (Nat.mul_comm _ _)⟩

end Work.ThmF.Prove.S3
