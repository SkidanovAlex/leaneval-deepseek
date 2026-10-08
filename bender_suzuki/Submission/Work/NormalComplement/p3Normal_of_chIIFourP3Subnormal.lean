import Mathlib
import Submission.Work.NormalComplement._design.Vocab
import Submission.Work.NormalComplement.Sections

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- The design's `P3NormalProp` was stated for a *normal* `Y`; `Submission.Blueprint` now carries
the subnormal form `ChIIFourP3SubnormalProp` (with `IsSubnormalIn Y X`, the reflexive-transitive
closure of normal inclusions), so the normal case follows at once:
`Y ≤ X` and `X ≤ Subgroup.normalizer (Y : Set G)` give `(Y.subgroupOf X).Normal`
(`Subgroup.normal_subgroupOf_iff_le_normalizer`), hence `IsSubnormalIn Y X` by the single-step
constructor of `ReflTransGen`; every other hypothesis is identical, and the conclusion of
`P3NormalProp` is a conjunct-weakening of the subnormal one (`S ≤ F ⊓ H` splits, and the extra
index clause is discarded). -/
theorem p3Normal_of_chIIFourP3Subnormal
    (h : Submission.Blueprint.ChIIFourP3SubnormalProp) :
    Work.NormalComplement.Design.P3NormalProp := by
  intro G _ _ sit H hse t ht htH X Y hX hY hYX hXN hk
  -- `Y` is normal in `X`, hence subnormal.
  have hsub : Submission.Blueprint.IsSubnormalIn Y X :=
    Relation.ReflTransGen.single
      ⟨hYX, (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXN⟩
  -- Apply the subnormal form and weaken its conclusion.
  have hc := h G sit H hse t ht htH X Y hX hY hsub hk
  refine ⟨hc.1, ?_⟩
  obtain ⟨S, hSp, hSFH, _hSix, hSN, hStp, hSup⟩ := hc.2
  exact ⟨S, hSp, (le_inf_iff.mp hSFH).1, (le_inf_iff.mp hSFH).2, hSN, hStp, hSup⟩

end Work.NormalComplement
