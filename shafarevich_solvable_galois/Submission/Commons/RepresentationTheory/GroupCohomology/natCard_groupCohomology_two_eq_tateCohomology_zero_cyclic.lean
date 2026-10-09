import Mathlib
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.RepresentationTheory.GroupCohomology

/-- **Cyclic periodicity, cardinality form.**  For a finite cyclic group `G` and a `ℤ[G]`-module
`V`, the second group cohomology `H²(G, V)` has the same cardinality as the zeroth Tate
cohomology `Ĥ⁰(G, V)`.

Route: for cyclic `G` the periodicity isomorphism `H²(G,V) ≅ Ĥ⁰(G,V)` can be obtained by
combining `Mathlib.RepresentationTheory.Homological.GroupCohomology`'s description of `H²` for
cyclic groups (via the "even degree" iso `groupCohomologyπEven_eq_zero_iff`, computing
`H²(G,V) ≅ V^G / N V`) with `tateCohomology_zero_iso`, which identifies `Ĥ⁰(G,V)` with
`V^G ⧸ (N V ∩ V^G)`; use `Nonempty` elimination for the linear equivalences and `letI` for the
`Module ℤ` instances on the submodules. -/
theorem natCard_groupCohomology_two_eq_tateCohomology_zero_cyclic
    {G V : Type} [Group G] [Fintype G] [IsCyclic G] [AddCommGroup V] [Module ℤ V]
    (ρ : Representation ℤ G V) :
    Nat.card ↑(groupCohomology (Rep.of ρ) 2) = Nat.card ↑(tateCohomology (Rep.of ρ) 0) := by
  -- A cyclic group is commutative; install the (definitionally compatible) `CommGroup`
  -- structure so that the periodicity theorem for finite commutative groups applies.
  letI : CommGroup G := IsCyclic.commGroup
  -- Pick a generator: every element is a power of it.
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  -- Periodicity in degree two for a finite cyclic group, in cardinality form.
  exact natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic g hg (Rep.of ρ)

end Commons.RepresentationTheory.GroupCohomology
