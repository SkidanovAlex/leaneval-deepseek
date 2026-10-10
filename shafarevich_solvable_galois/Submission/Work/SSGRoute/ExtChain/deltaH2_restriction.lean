import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Algebra.Group.Subgroup
import Submission.Work.SSGRoute.PT.akH2Setup
import Submission.Work.SSGRoute.PT.resH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of the connecting map `δ` to a subgroup

The connecting map `S.deltaH2 : H¹(G,P) →+ H²(G,M)` of a short exact sequence
`0 → M → N → P → 0` of discrete `G`-modules (`Work.AbsoluteKummer.ShortExactSeq`) commutes with
restriction to a subgroup `U ≤ G`:

  `resH2 U (S.deltaH2 x) = (S|U).deltaH2 (resH1 U x)`,

where `S|U` is the *same* short exact sequence of `↥U`-modules (the underlying maps and modules are
unchanged; only the action is restricted) and `resH1`/`resH2` are the restriction maps of the
continuous model (`Work.SSGRoute.PT.resH1`, `Work.SSGRoute.PT.resH2`).

This is the group-naturality of the connecting map, i.e. the `δ`-part of the "comparison square"
of the E1a node `Work.SSGRoute.ext_sha2_bridge` (`Submission/Work/SSGRoute/NOTE_e1a_session5.md`
§0–§1): the per-place comparison of the global chain with the local one needs
`res_{D_A}(δ x) = δ_{D_A}(res_{D_A} x)`, which is not a formality of the `Nonempty`-witnessed
dictionaries but *is* formal for the connecting map once the two short exact sequences are related
cochain-wise.  The proof is the same cochain computation as `deltaH2_natural`
(`Submission/Work/SSGRoute/ExtChain/e1aDelta_natural.lean`), with the coefficient morphism of that
lemma specialised to the identity and `resZ2`/`resZ1` in place of `mapZ2`/`mapZ1`.
-/

namespace Work.SSGRoute.ExtChain

open scoped Classical

noncomputable section

/-- **The restriction of a short exact sequence of discrete `G`-modules to a subgroup `U ≤ G`**:
the same modules and the same two maps, with the action restricted to `U` (and the discreteness
transferred by `H2Fin.isDiscreteModule_subgroup`). -/
def restrictSES {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) (U : Subgroup G) :
    Work.AbsoluteKummer.ShortExactSeq ↥U M N P where
  iota := S.iota
  pi := S.pi
  iota_equivariant := fun u m => S.iota_equivariant (u : G) m
  pi_equivariant := fun u n => S.pi_equivariant (u : G) n
  iota_injective := S.iota_injective
  pi_surjective := S.pi_surjective
  range_iota_eq_ker_pi := S.range_iota_eq_ker_pi
  isDiscreteM := Work.SSGRoute.PT.H2Fin.isDiscreteModule_subgroup U S.isDiscreteM
  isDiscreteN := Work.SSGRoute.PT.H2Fin.isDiscreteModule_subgroup U S.isDiscreteN
  isDiscreteP := Work.SSGRoute.PT.H2Fin.isDiscreteModule_subgroup U S.isDiscreteP

@[simp] theorem restrictSES_iota {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) (U : Subgroup G) :
    (restrictSES S U).iota = S.iota := rfl

@[simp] theorem restrictSES_pi {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) (U : Subgroup G) :
    (restrictSES S U).pi = S.pi := rfl

/-- **The connecting map commutes with restriction to a subgroup.** -/
theorem deltaH2_restriction {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) (U : Subgroup G)
    (x : Work.AbsoluteKummer.H1 G P) :
    Work.SSGRoute.PT.resH2 U (S.deltaH2 x)
      = (restrictSES S U).deltaH2 (Work.SSGRoute.PT.H2Fin.resH1 U P x) := by
  let S' : Work.AbsoluteKummer.ShortExactSeq ↥U M N P := restrictSES S U
  have hπ : S'.pi = S.pi := rfl
  induction x using Work.AbsoluteKummer.SES.H1_induction_on with
  | h c =>
    rw [Work.SSGRoute.PT.H2Fin.resH1_H1π, Work.AbsoluteKummer.ShortExactSeq.deltaH2_H1π,
      Work.AbsoluteKummer.ShortExactSeq.deltaH2_H1π, Work.SSGRoute.PT.resH2_H2π]
    rw [Work.AbsoluteKummer.H2π_eq_iff]
    -- the primitive of the difference of the two `δ`-cocycles
    have hlift : ∀ u : ↥U, S'.pi ((fun v : ↥U => S.liftCochainC (c : G → P) v) u
        - S'.liftCochainC (Work.SSGRoute.PT.H2Fin.resZ1 U P c) u) = 0 := by
      intro u
      rw [map_sub, S'.pi_liftCochainC, hπ, S.pi_liftCochainC]
      exact sub_self _
    let k : ↥U → M := fun u => S'.iotaInv ((fun v : ↥U => S.liftCochainC (c : G → P) v) u
      - S'.liftCochainC (Work.SSGRoute.PT.H2Fin.resZ1 U P c) u)
    have hk : ∀ u : ↥U, S'.iota (k u) = (fun v : ↥U => S.liftCochainC (c : G → P) v) u
        - S'.liftCochainC (Work.SSGRoute.PT.H2Fin.resZ1 U P c) u :=
      fun u => S'.iota_iotaInv (S'.mem_range_of_mem_ker (hlift u))
    have hklc : k ∈ Work.AbsoluteKummer.C1c ↥U M :=
      Work.AbsoluteKummer.IsLocallyConstant.map S'.iotaInv
        ((S.isLocallyConstant_liftCochainC
            (Work.AbsoluteKummer.isLocallyConstant_of_mem_Z1 c.2)).comp
              continuous_subtype_val |>.sub
          (S'.isLocallyConstant_liftCochainC
            (Work.AbsoluteKummer.isLocallyConstant_of_mem_Z1
              (Work.SSGRoute.PT.H2Fin.resZ1 U P c).2)))
    refine (Work.AbsoluteKummer.mem_B2_iff _).mpr ⟨k, hklc, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    apply S'.iota_injective
    have hA : S'.iota ((Work.GroupCohomology.d1 ↥U M) k (g, h))
        = (Work.GroupCohomology.d1 ↥U N)
            (Work.GroupCohomology.mapCochain1 ↥U S'.iota k) (g, h) := by
      have hh := congrFun (Work.GroupCohomology.mapCochain2_d1 ↥U S'.iota S'.iota_equivariant k)
        (g, h)
      rwa [Work.GroupCohomology.mapCochain2_apply] at hh
    have hmap : Work.GroupCohomology.mapCochain1 ↥U S'.iota k
        = (fun v : ↥U => S.liftCochainC (c : G → P) v)
          - S'.liftCochainC (Work.SSGRoute.PT.H2Fin.resZ1 U P c) := by
      funext u
      exact hk u
    -- the two summands of `d¹ (mapCochain1 S'.iota k)`
    have h1 : (Work.GroupCohomology.d1 ↥U N)
        (fun v : ↥U => S.liftCochainC (c : G → P) v) (g, h)
        = S.iota ((S.deltaCocycleC c : G × G → M) ((g : G), (h : G))) := by
      rw [show (Work.GroupCohomology.d1 ↥U N)
            (fun v : ↥U => S.liftCochainC (c : G → P) v) (g, h)
          = (Work.GroupCohomology.d1 G N) (S.liftCochainC (c : G → P)) ((g : G), (h : G))
        from by
          simp only [Work.GroupCohomology.d1_apply, Subgroup.smul_def, Subgroup.coe_mul]]
      rw [← S.iota_deltaCocycleC c (g : G) (h : G)]
    have h2 : (Work.GroupCohomology.d1 ↥U N)
        (S'.liftCochainC (Work.SSGRoute.PT.H2Fin.resZ1 U P c)) (g, h)
        = S'.iota ((S'.deltaCocycleC (Work.SSGRoute.PT.H2Fin.resZ1 U P c) :
            ↥U × ↥U → M) (g, h)) :=
      (S'.iota_deltaCocycleC _ g h).symm
    have hsub : (Work.GroupCohomology.d1 ↥U N)
        (Work.GroupCohomology.mapCochain1 ↥U S'.iota k) (g, h)
        = S'.iota ((Work.SSGRoute.PT.resCochain2 U (S.deltaCocycleC c : G × G → M) :
              ↥U × ↥U → M) (g, h)
            - (S'.deltaCocycleC (Work.SSGRoute.PT.H2Fin.resZ1 U P c) :
              ↥U × ↥U → M) (g, h)) := by
      rw [hmap, map_sub, Pi.sub_apply, h1, h2, map_sub]
      rfl
    rw [hA, hsub]
    simp only [Work.SSGRoute.PT.resCochain2_apply, Work.SSGRoute.PT.resZ2]
    rfl

end

end Work.SSGRoute.ExtChain

