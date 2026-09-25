import Mathlib

/-!
# Subgroups with cyclic quotient of a finite abelian group

For a finite abelian group `G`, the intersection of all subgroups `H ≤ G` whose quotient `G ⧸ H`
is cyclic is trivial.

This is the group-theoretic input to the reduction of the ideal-theoretic Artin reciprocity law
for an abelian extension `L/K` to the cyclic case (Lang, *Algebraic Number Theory*, 2nd ed.,
Chapter X, Theorem 3): an element of `Gal(L/K)` is trivial if and only if its images in all the
cyclic quotients `Gal(L/K) ⧸ H` are trivial, i.e.
`⋂ {H : G ⧸ H cyclic} H = ⊥`.

The proof uses the structure theorem for finite abelian groups: a finite abelian group is a
product of finite cyclic groups, and the kernels of the coordinate projections are subgroups with
cyclic quotient whose intersection is trivial.
-/

set_option linter.style.haveILetI false

namespace NK.CFTLib.ArtinReciprocityIdeal

/-- The quotient of a group by the kernel of a homomorphism into a cyclic group is cyclic. -/
lemma isCyclic_quotient_ker {G C : Type*} [Group G] [Group C] [IsCyclic C] (π : G →* C) :
    IsCyclic (G ⧸ π.ker) := by
  haveI : IsCyclic π.range :=
    isCyclic_of_injective (Subgroup.subtype π.range) (Subgroup.subtype_injective π.range)
  exact isCyclic_of_injective (QuotientGroup.quotientKerEquivRange π).toMonoidHom
    (QuotientGroup.quotientKerEquivRange π).injective

theorem iInf_subgroup_isCyclic_quotient {G : Type*} [CommGroup G] [Finite G] :
    (⨅ H : {H : Subgroup G // IsCyclic (G ⧸ H)}, (H.1 : Subgroup G)) = ⊥ := by
  classical
  obtain ⟨ι, _, n, _, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  -- Every coordinate projection is a homomorphism into a cyclic group; its kernel is in the
  -- family, and the intersection of all these kernels is trivial.
  have hmem : ∀ i : ι, x ∈ ((Pi.evalMonoidHom (fun i : ι => Multiplicative (ZMod (n i))) i).comp
      e.toMonoidHom).ker := by
    intro i
    exact (Subgroup.mem_iInf
      (S := fun H : {H : Subgroup G // IsCyclic (G ⧸ H)} => (H.1 : Subgroup G))).mp hx
      ⟨_, isCyclic_quotient_ker _⟩
  have hx1 : e x = 1 := by
    funext i
    exact MonoidHom.mem_ker.mp (hmem i)
  exact e.injective (hx1.trans (map_one e).symm)

end NK.CFTLib.ArtinReciprocityIdeal
