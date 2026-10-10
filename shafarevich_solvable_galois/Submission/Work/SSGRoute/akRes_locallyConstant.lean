import Mathlib.Topology.Constructions
import Mathlib.Algebra.Group.Subgroup.Actions
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restricting locally constant `2`-cocycles to a subgroup

`Work.AbsoluteKummer.Z2 G M` is the subgroup of locally constant `2`-cocycles
(`GroupCohomology.Z2 G M ⊓ C2c G M`).  The task is to record that *restriction to a subgroup*
(plain function restriction on `↥H × ↥H → M`) preserves this: the cocycle identity transfers
verbatim through the coerced `DistribMulAction ↥H M`, and local constancy is preserved by
precomposition with the continuous map `↥H × ↥H → G × G`
(`Work.AbsoluteKummer.IsLocallyConstant.comp`).

This is the missing ingredient for defining a restriction map on the *continuous* second
cohomology `Work.AbsoluteKummer.H2` (`AbsoluteKummer` currently only has coefficient changes
`mapH2`), which is needed to compare the *continuous* restriction of the canonical chain
`PT.e1aChainC` with its abstract restriction used in
`PT/e1aBetaCan_localDictionary_fin_compat` (see the note
`PT/NOTE_e1aBetaCan_localDictionary_fin_compat.md` §3).
-/

namespace Work.AbsoluteKummer

/-- **Restriction of a locally constant `2`-cocycle to a subgroup is a locally constant
`2`-cocycle.** -/
theorem akRes_locallyConstant {G : Type} [TopologicalSpace G] [Group G] (H : Subgroup G)
    (M : Type) [AddCommGroup M] [DistribMulAction G M] (c : G × G → M)
    (hc : c ∈ Work.AbsoluteKummer.Z2 G M) :
    (fun q : ↥H × ↥H => c (q.1, q.2)) ∈ Work.AbsoluteKummer.Z2 ↥H M := by
  rw [Work.AbsoluteKummer.mem_Z2_iff] at hc ⊢
  have hsmul : ∀ (g : ↥H) (x : M), g • x = (g : G) • x := fun g x => rfl
  refine ⟨fun g h k => ?_, ?_⟩
  · have h := hc.1 (g : G) (h : G) (k : G)
    rw [hsmul]
    simpa using h
  · have hcont : Continuous (fun q : ↥H × ↥H => ((q.1 : G), (q.2 : G))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact hc.2.comp hcont

end Work.AbsoluteKummer
