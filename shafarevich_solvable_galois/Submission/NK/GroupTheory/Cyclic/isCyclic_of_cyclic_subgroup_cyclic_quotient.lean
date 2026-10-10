import Mathlib.GroupTheory.SpecificGroups.Cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GroupTheory.Cyclic

/-- If a finite abelian group `A` has a cyclic subgroup `S` whose quotient `A ⧸ S` is also
cyclic, and the orders of `S` and `A ⧸ S` are coprime, then `A` is cyclic.

Proof: the exponent of `A` is divisible by both `|S|` and `|A ⧸ S|`, hence by their product,
which is `|A|`; conversely the exponent always divides `|A|`.  So the exponent of `A` equals its
cardinality, and a finite abelian group is cyclic precisely when its exponent equals its order. -/
theorem isCyclic_of_cyclic_subgroup_cyclic_quotient {A : Type*} [CommGroup A] [Finite A]
    (S : Subgroup A) (hS : IsCyclic ↥S) (hQ : IsCyclic (A ⧸ S))
    (hcop : (Nat.card ↥S).Coprime (Nat.card (A ⧸ S))) : IsCyclic A := by
  rw [IsCyclic.iff_exponent_eq_card]
  -- The exponent of a cyclic group equals its cardinality.
  have hSexp : Monoid.exponent ↥S = Nat.card ↥S := IsCyclic.exponent_eq_card
  have hQexp : Monoid.exponent (A ⧸ S) = Nat.card (A ⧸ S) := IsCyclic.exponent_eq_card
  -- The exponent of a quotient divides the exponent of the group...
  have h1 : Nat.card (A ⧸ S) ∣ Monoid.exponent A := by
    rw [← hQexp]
    exact MonoidHom.exponent_dvd (QuotientGroup.mk'_surjective S)
  -- ... and so does the exponent of a subgroup.
  have h2 : Nat.card ↥S ∣ Monoid.exponent A := by
    rw [← hSexp]
    exact Monoid.exponent_dvd_of_monoidHom S.subtype S.subtype_injective
  -- Coprimality upgrades divisibility by the two factors to divisibility by the product,
  -- which is the cardinality of `A`.
  have h3 : Nat.card A ∣ Monoid.exponent A := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup S]
    exact hcop.symm.mul_dvd_of_dvd_of_dvd h1 h2
  -- The exponent divides the cardinality in general.
  exact Nat.dvd_antisymm Group.exponent_dvd_nat_card h3

end NK.GroupTheory.Cyclic
