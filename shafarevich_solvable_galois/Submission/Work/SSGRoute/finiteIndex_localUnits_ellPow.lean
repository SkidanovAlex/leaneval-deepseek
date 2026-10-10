import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Group.Units
import Submission.Work.SSGRoute.ges_escape_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `𝔭`-adic `p`-th powers in the local units have finite index in the local units

For a number field `K`, a finite prime `𝔭` of `K` and a prime `p`, the group

`(𝒪_𝔭ˣ) ∩ (K_𝔭ˣ)^p = {u ∈ 𝒪_𝔭ˣ | u is a `p`-th power in `K_𝔭ˣ`}`

has finite index in the group `𝒪_𝔭ˣ` of local units.

The argument is purely topological: the ring of integers `𝒪_𝔭` of the completion `K_𝔭` is
compact, hence so is the group `𝒪_𝔭ˣ` of its units; the subgroup `(K_𝔭ˣ)^p` is *open* in
`K_𝔭ˣ` (`NK.UchidaKummer.Approximation.isOpenEllPowSubgroup`, proved by Hensel's lemma / the
`p`-adic logarithm), so its trace on the compact group `𝒪_𝔭ˣ` is open, and an open subgroup of a
compact group has finite index.

## Main results

* `Work.SSGRoute.subgroupOf_finiteIndex_of_isOpen_of_isCompact`: an open subgroup of a compact
  topological group intersected with a compact subgroup has finite index in it.
* `Work.SSGRoute.finiteIndex_localUnits_ellPow`: the statement above.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped NumberField
open Topology

namespace Work.SSGRoute

/-- **An open subgroup of a compact group has finite index in it.**  More precisely, if `A` is a
compact subgroup of a topological group `G` and `B ≤ G` is an open subgroup, then the subgroup
`B ∩ A = B.subgroupOf A` has finite index in `A`.

Indeed `A ⧸ (B.subgroupOf A)` is a quotient of the compact group `A` (hence compact), and the
fiber over the class of `a ∈ A` is the translate `a · (B ∩ A)` of the open subgroup `B ∩ A`,
so all singletons of the quotient are open: the quotient is discrete, hence finite. -/
theorem subgroupOf_finiteIndex_of_isOpen_of_isCompact {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B : Subgroup G} (hA : IsCompact (A : Set G))
    (hB : IsOpen (B : Set G)) : (B.subgroupOf A).FiniteIndex := by
  haveI : CompactSpace ↥A := isCompact_iff_compactSpace.mp hA
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  haveI : CompactSpace (↥A ⧸ B.subgroupOf A) := inferInstance
  haveI : DiscreteTopology (↥A ⧸ B.subgroupOf A) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    -- the topology on the quotient is the coinduced one, so it suffices to open the preimage
    rw [(QuotientGroup.isQuotientMap_mk (B.subgroupOf A)).eq_coinduced, isOpen_coinduced]
    -- that preimage is the trace of the open coset `B` on `A`
    have hpre : QuotientGroup.mk ⁻¹' ({QuotientGroup.mk a} : Set (↥A ⧸ B.subgroupOf A)) =
        (fun x : ↥A => ((x : G)⁻¹ * (a : G))) ⁻¹' (B : Set G) := by
      ext x
      rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_preimage, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [hpre]
    exact hB.preimage ((continuous_inv.comp continuous_subtype_val).mul continuous_const)
  exact finite_of_compact_of_discrete

/-- **The ring of integers of a `𝔭`-adic completion is compact**, as a subset of the completion. -/
theorem isCompact_adicCompletionIntegers (K : Type*) [Field K] [NumberField K]
    (𝔭 : NK.Chebotarev.PrimeIdeal K) :
    IsCompact ((𝔭.adicCompletionIntegers K : Set (𝔭.adicCompletion K))) := by
  haveI : CompactSpace (𝔭.adicCompletionIntegers K) :=
    Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers K 𝔭
  have h := (Subtype.isCompact_iff (p := fun x : 𝔭.adicCompletion K =>
    x ∈ 𝔭.adicCompletionIntegers K) (s := Set.univ)).mp isCompact_univ
  simpa using h

/-- **The local units at a finite place are compact**: they are the units of the compact ring of
integers, and the units of a compact submonoid of a topological monoid form a compact subset of
the unit group. -/
theorem isCompact_localUnits (K : Type*) [Field K] [NumberField K]
    (𝔭 : NK.Chebotarev.PrimeIdeal K) :
    IsCompact ((NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭) :
      Set (𝔭.adicCompletion K)ˣ)) := by
  have hS : IsCompact ((𝔭.adicCompletionIntegers K : Set (𝔭.adicCompletion K))) :=
    isCompact_adicCompletionIntegers K 𝔭
  have hunits := Submonoid.units_isCompact hS
  simpa [NK.GlobalCFT.Place.localUnits_ofFinite] using hunits

/-- **The `p`-th powers inside the local units have finite index.**

The subgroup of local units `u ∈ 𝒪_𝔭ˣ` that are `p`-th powers in `K_𝔭ˣ` is open in the compact
group `𝒪_𝔭ˣ` — it is the trace of the open subgroup `(K_𝔭ˣ)^p` — hence of finite index. -/
theorem finiteIndex_localUnits_ellPow (K : Type*) [Field K] [NumberField K]
    (𝔭 : NK.Chebotarev.PrimeIdeal K) (p : ℕ) [Fact p.Prime] :
    ((NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p).subgroupOf
      (NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭))).FiniteIndex :=
  subgroupOf_finiteIndex_of_isOpen_of_isCompact (isCompact_localUnits K 𝔭)
    ((NK.UchidaKummer.Approximation.isOpenEllPowSubgroup K p (Fact.out)) 𝔭)

end Work.SSGRoute
