import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.AppXIDickson

/-- **A finite nilpotent group whose Sylow subgroups are all cyclic is cyclic.**

This is Mathlib's `IsZGroup.instIsCyclicOfFiniteOfIsNilpotent`: a finite nilpotent group is the
direct product of its Sylow subgroups, so if these are cyclic (hence abelian, of pairwise coprime
order) the group is a direct product of cyclic groups of pairwise coprime order, i.e. cyclic. -/

theorem isCyclic_of_odd_nilpotent_ellCyclic {M : Type} [Group M] [Finite M]
    (hnil : Group.IsNilpotent M) {C : Subgroup M} (hodd : Odd (Nat.card ↥C))
    (hℓ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ B : Subgroup M, IsPGroup ℓ ↥B → IsCyclic ↥B) :
    IsCyclic ↥C := by
  -- `C` is finite nilpotent (a subgroup of the nilpotent group `M`).
  haveI : Group.IsNilpotent M := hnil
  haveI : Group.IsNilpotent ↥C := Subgroup.isNilpotent C
  -- It suffices to show that `C` is a Z-group, i.e. that all its Sylow subgroups are cyclic.
  haveI hZ : IsZGroup ↥C := ⟨fun p hp P => by
    rcases eq_or_ne p 2 with rfl | hp2
    · -- The `2`-Sylow subgroup of the odd-order group `C` is trivial, hence cyclic.
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hnotdvd : ¬ 2 ∣ Nat.card ↥C :=
        fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
      have hcard : Nat.card ↥P = 1 := by
        change Nat.card ↥(↑P : Subgroup ↥C) = 1
        rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hnotdvd, pow_zero]
      haveI : Subsingleton ↥P := (Nat.card_eq_one_iff_unique.mp hcard).1
      exact isCyclic_of_subsingleton
    · -- Odd prime: transport the `ℓ`-subgroup hypothesis across the injection `C ↪ M`.
      exact (Subgroup.equivMapOfInjective (↑P : Subgroup ↥C) (Subgroup.subtype C)
          (Subgroup.subtype_injective C)).isCyclic.mpr
        (hℓ p hp hp2 _ (P.isPGroup'.map (Subgroup.subtype C)))
  ⟩
  exact inferInstance

end Work.AppXIDickson
