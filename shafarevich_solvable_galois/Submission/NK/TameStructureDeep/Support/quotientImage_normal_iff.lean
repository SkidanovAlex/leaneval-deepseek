import Mathlib
import Submission.NK.TameStructureDeep.Defs
import Submission.NK.LocalTame.Basic
import Submission.NK.TameData.Inertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Support

/-- **Normality of `J/V` is normality of `J`, over `V`.**  For `V ◁ G` and a subgroup `J ≥ V`, the
image of `J` in `G ⧸ V` is normal exactly when `J` is normal in `G`.  The direction `⟸` is
`NK.TameData.Inertia.quotientImage_normal` (which needs no hypothesis at all); for `⟹` one pulls
back along `QuotientGroup.mk' V`: `(quotientImage V J).comap (QuotientGroup.mk' V) = V ⊔ J = J` by
`QuotientGroup.comap_map_mk'` and `V ≤ J`, and a preimage of a normal subgroup is normal.

This is the translation step that lets the normality clauses of
`NK.LocalTame.IsMaxNormalProCyclicInQuotient` be read inside `G` rather than inside `G ⧸ V`.  It is
used for every `J ≥ V` in the maximality clause — the case `J = I` is
`NK.TameStructureDeep.Support.isMaxNormalProCyclicInQuotient_normal` — and it is what makes
`NK.TameStructureDeep.Support.isMaxNormalProCyclicInQuotient_iff` (the subgroup form of the
predicate) usable clause by clause; that file proves its normality clauses with this result.

File: `Submission/Work/TameStructureDeep/Support/quotientImage_normal_iff.lean`, namespace
`NK.TameStructureDeep.Support`, importing `Submission.NK.TameStructureDeep.Defs`. -/
theorem quotientImage_normal_iff {G : Type*} [Group G] {V J : Subgroup G} [V.Normal] (h : V ≤ J) :
    (NK.LocalTame.quotientImage V J).Normal ↔ J.Normal := by
  refine ⟨fun hJ => ?_, fun hJ => NK.TameData.quotientImage_normal hJ⟩
  -- `V ≤ J` makes `J` the full preimage of its image in `G ⧸ V`
  have hcomap : (NK.LocalTame.quotientImage V J).comap (QuotientGroup.mk' V) = J := by
    rw [NK.LocalTame.quotientImage, QuotientGroup.comap_map_mk', sup_eq_right.mpr h]
  -- a preimage of a normal subgroup is normal
  have hn : ((NK.LocalTame.quotientImage V J).comap (QuotientGroup.mk' V)).Normal :=
    hJ.comap _
  rwa [hcomap] at hn

end NK.TameStructureDeep.Support
