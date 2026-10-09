import Mathlib
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.SSGRoute.akRes_locallyConstant
import Submission.Work.SSGRoute.PT.e1aBetaCan_aux
import Submission.Work.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction on the continuous second cohomology `AbsoluteKummer.H2`

`Work.AbsoluteKummer.H2 G M` (locally constant `2`-cocycles modulo coboundaries of locally
constant `1`-cochains) carries no group restriction in the library: only *coefficient* changes
`mapH2` exist.  This file supplies the restriction to a subgroup `H ≤ G`, together with the
computation rule on classes of cocycles and the naturality square with the forgetful map
`Work.SSGRoute.PT.akToGCH2` into the *abstract* model `Work.GroupCohomology.H2`.

This is the missing comparison that lets one relate the hypothesis of
`Work.SSGRoute.PT.e1aBetaCan_localDictionary_fin_compat` (the *abstract* restriction
`resH2 H (akToGCH2 (e1aChainC y)) = 0`) with the *continuous* condition
`res_cont_H (e1aChainC y) = 0` used by the sibling node `PT/e1aChainC_localComparison`; see
`PT/NOTE_e1aBetaCan_localDictionary_fin_compat.md` §3.
-/

namespace Work.AbsoluteKummer

/-- Restriction of a locally constant `1`-cochain to a subgroup. -/
theorem akRes_locallyConstant1 {G : Type} [TopologicalSpace G] [Group G] (H : Subgroup G)
    (M : Type) [AddCommGroup M] [DistribMulAction G M] (f : G → M)
    (hf : f ∈ Work.AbsoluteKummer.C1c G M) :
    (fun h : ↥H => f (h : G)) ∈ Work.AbsoluteKummer.C1c ↥H M :=
  (Work.AbsoluteKummer.mem_C1c_iff _).mpr
    (((Work.AbsoluteKummer.mem_C1c_iff f).mp hf).comp continuous_subtype_val)

/-- The restriction of cocycles, as an additive map on the locally constant `2`-cocycles. -/
noncomputable def akResZ2 {G : Type} [TopologicalSpace G] [Group G] (H : Subgroup G)
    (M : Type) [AddCommGroup M] [DistribMulAction G M] :
    ↥(Work.AbsoluteKummer.Z2 G M) →+ ↥(Work.AbsoluteKummer.Z2 ↥H M) where
  toFun z := ⟨fun q : ↥H × ↥H => (z : G × G → M) (q.1, q.2),
    akRes_locallyConstant H M _ z.2⟩
  map_zero' := by
    apply Subtype.ext
    funext q
    rfl
  map_add' a b := by
    apply Subtype.ext
    funext q
    rfl

/-- **Restriction on the continuous second cohomology**, with its computation rule and its
naturality with the forgetful map `akToGCH2` into the abstract model. -/
theorem akH2_restriction_natural {G : Type} [TopologicalSpace G] [Group G] (H : Subgroup G)
    (M : Type) [AddCommGroup M] [DistribMulAction G M] :
    ∃ r : Work.AbsoluteKummer.H2 G M →+ Work.AbsoluteKummer.H2 ↥H M,
      (∀ (c : G × G → M) (hc : c ∈ Work.AbsoluteKummer.Z2 G M),
        r (Work.AbsoluteKummer.H2π G M ⟨c, hc⟩) =
          Work.AbsoluteKummer.H2π ↥H M
            ⟨fun q : ↥H × ↥H => c (q.1, q.2), akRes_locallyConstant H M c hc⟩) ∧
      (∀ x : Work.AbsoluteKummer.H2 G M,
        Work.SSGRoute.PT.akToGCH2 ↥H M (r x) =
          Work.GroupCohomology.resH2 G H (Work.SSGRoute.PT.akToGCH2 G M x)) := by
  classical
  -- the descent: the restriction of a continuous coboundary is a continuous coboundary on `H`
  have hdescent : (Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype ≤
      ((Work.AbsoluteKummer.H2π ↥H M).comp (akResZ2 H M)).ker := by
    intro z hz
    refine AddMonoidHom.mem_ker.mpr ?_
    have hz' : (z : G × G → M) ∈ Work.AbsoluteKummer.B2 G M := AddSubgroup.mem_comap.mp hz
    show Work.AbsoluteKummer.H2π ↥H M (akResZ2 H M z) = 0
    rw [Work.AbsoluteKummer.H2π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_comap]
    show ((akResZ2 H M z : ↥(Work.AbsoluteKummer.Z2 ↥H M)) : ↥H × ↥H → M)
      ∈ Work.AbsoluteKummer.B2 ↥H M
    rw [Work.AbsoluteKummer.mem_B2_iff] at hz' ⊢
    obtain ⟨f, hf, hfc⟩ := hz'
    refine ⟨fun h : ↥H => f (h : G), akRes_locallyConstant1 H M f hf, ?_⟩
    funext q
    obtain ⟨g, h⟩ := q
    have hcoe : ((g * h : ↥H) : G) = (g : G) * (h : G) := rfl
    have hsmul : g • f (h : G) = (g : G) • f (h : G) := rfl
    rw [Work.GroupCohomology.d1_apply, hsmul, hcoe]
    exact congrFun hfc ((g : G), (h : G))
  refine ⟨QuotientAddGroup.lift _ ((Work.AbsoluteKummer.H2π ↥H M).comp (akResZ2 H M)) hdescent,
    ?_, ?_⟩
  · intro c hc
    show QuotientAddGroup.lift _ _ hdescent (↑(⟨c, hc⟩ : ↥(Work.AbsoluteKummer.Z2 G M)))
      = Work.AbsoluteKummer.H2π ↥H M ⟨fun q : ↥H × ↥H => c (q.1, q.2),
          akRes_locallyConstant H M c hc⟩
    rw [QuotientAddGroup.lift_mk', AddMonoidHom.comp_apply]
    rfl
  · intro x
    refine QuotientAddGroup.induction_on x ?_
    intro z
    rw [QuotientAddGroup.lift_mk', AddMonoidHom.comp_apply, Work.SSGRoute.PT.akToGCH2_H2π]
    rw [show ((z : ↥(Work.AbsoluteKummer.Z2 G M)) : Work.AbsoluteKummer.H2 G M)
        = Work.AbsoluteKummer.H2π G M z from rfl]
    rw [Work.SSGRoute.PT.akToGCH2_H2π, Work.GroupCohomology.resH2_H2π]
    apply congrArg (Work.GroupCohomology.H2π ↥H M)
    apply Subtype.ext
    funext q
    rw [Work.SSGRoute.PT.akZ2ToGCZ2_coe, Work.GroupCohomology.resZ2_coe,
      Work.GroupCohomology.resCochain2_apply]
    rfl

end Work.AbsoluteKummer
