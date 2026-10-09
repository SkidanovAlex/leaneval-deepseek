/-
# Restricting a module action to a subgroup, and discreteness of the restriction

Two inputs of the coprime-index wiring of local Tate duality in degrees 0/2
(`PTUr/NOTE_E7_h02_frontier_measured.md` §5, step 1) concern the *open subgroup*
`U ≤ ↥(decomp k A)` rather than the decomposition group itself:

* the `↥U`-action on the coefficient module `N = DualMod p (M ⊗ T)`, obtained from the
  `↥(decomp k A)`-action by `DistribMulAction.compHom` (the pattern of `mkbUnitsDecomp`,
  `PT/mkb_ld02_defs.lean`, at the `G` level);
* the discreteness `IsDiscreteModule ↥U N` of that action, needed by the dévissage SES
  (`PT/DevissageSESFinal.lean`'s `devissageSES` takes `IsDiscreteModule G M` *and*
  `IsDiscreteModule U M`).

The discreteness is *formal*: for the `compHom` action the stabiliser in `U` is the preimage of the
stabiliser in `G` under the inclusion `U.subtype`, and open subgroups pull back to open subgroups
because `↥U` carries the subspace topology.  Because `IsDiscreteModule`'s typeclass context is not
determined by `↥U` alone, the *content* is stated here in the preimage form (no instance juggling);
the consumer introduces the action with `compHomSubgroupAction` via `letI` and rewrites with
`MulAction.stabilizer` as in `Work.SSGRoute.isDiscreteModule_decomp_of_compat`.
-/
import Mathlib
import Submission.Work.SSGRoute.kummerBase_euler_ses_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **The action of a subgroup `U ≤ G` on a `G`-module `N`**, restricted along the inclusion
`U.subtype : ↥U →* G`.  (At the `G`-level this is `mkbUnitsDecomp`; here it is stated for a general
subgroup so that it can be used at `U ≤ ↥(decomp k A)`.) -/
noncomputable def compHomSubgroupAction (G : Type*) [Group G] (N : Type*) [AddMonoid N]
    [DistribMulAction G N] (U : Subgroup G) : DistribMulAction ↥U N :=
  DistribMulAction.compHom N U.subtype

/-- **Discreteness passes to subgroups** (content form, action instance-free): the stabilisers of
the restricted action are the preimages of the stabilisers of the ambient action. -/
theorem isDiscreteModule_preimage_subtype {G : Type*} [Group G] [TopologicalSpace G]
    {N : Type*} [AddMonoid N] [DistribMulAction G N]
    (h : ∀ n : N, IsOpen (MulAction.stabilizer G n : Set G)) (U : Subgroup G) :
    ∀ n : N, IsOpen (Subgroup.subtype U ⁻¹'
      (MulAction.stabilizer G n : Set G) : Set ↥U) :=
  fun n => (h n).preimage continuous_subtype_val

/-- The stabiliser identity that turns the previous lemma into `IsDiscreteModule ↥U N` for the
`compHom` action: for `u : ↥U`, `u` stabilises `n` for the restricted action iff its image in `G`
does. -/
theorem stabilizer_subtype_eq_preimage {G : Type*} [Group G] {N : Type*} [AddMonoid N]
    [DistribMulAction G N] (U : Subgroup G) (n : N) :
    letI : DistribMulAction ↥U N := compHomSubgroupAction G N U
    (MulAction.stabilizer ↥U n : Set ↥U)
      = Subgroup.subtype U ⁻¹' (MulAction.stabilizer G n : Set G) := by
  letI : DistribMulAction ↥U N := compHomSubgroupAction G N U
  ext u
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage]
  rfl

/-- **The concrete input of the coprime wiring**: for `N` a module with the compatibility action of
the decomposition group, the stabilisers of the `↥U`-action (obtained by `compHom`) are the
preimages of open subgroups, hence open, for every subgroup `U ≤ ↥(decomp k A)`. -/
theorem isDiscreteModule_decomp_subgroup_preimage (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (A : ValuationSubring Ω) (N : Type)
    [AddCommGroup N] [DistribMulAction (K ≃ₐ[k] K) N]
    [DistribMulAction ↥(SSGRoute.decomp k A) N]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A)) (n : N),
      h • n = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • n)
    (U : Subgroup ↥(SSGRoute.decomp k A)) :
    ∀ n : N, IsOpen (Subgroup.subtype U ⁻¹'
      (MulAction.stabilizer ↥(SSGRoute.decomp k A) n : Set ↥(SSGRoute.decomp k A)) :
        Set ↥U) :=
  isDiscreteModule_preimage_subtype
    (Work.SSGRoute.isDiscreteModule_decomp_of_compat k Ω K A N hcompat) U

end Work.SSGRoute.PT
