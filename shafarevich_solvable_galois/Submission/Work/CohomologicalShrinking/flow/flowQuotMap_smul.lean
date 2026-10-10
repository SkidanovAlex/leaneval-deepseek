import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Submission.Work.CohomologicalShrinking.Semidirect
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.flow

open Work.CohomologicalShrinking

theorem flowQuotMap_smul (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (g : G) (x : flowQuotient p G m i j) :
    flowQuotMap p G i j Φ (g • x) = g • flowQuotMap p G i j Φ x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) x
  have hP : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulAut G _ g).surjective
  have hKP : (flowTerm p G m i j).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = flowTerm p G m i j :=
    map_refinedTerm_eq p
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g) i j
  have hQ : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) g).toMonoidHom
      = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulAut G _ g).surjective
  have hKQ : (flowTerm p G n i j).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) g).toMonoidHom
      = flowTerm p G n i j :=
    map_refinedTerm_eq p
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) g) i j
  have keyP : g • (QuotientGroup.mk'
        ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y)
      = QuotientGroup.mk'
        ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
        (Work.Shrinking.subAut ⊤ g hP y) := by
    change Work.Shrinking.quotAut ⊤ (flowTerm p G m i j) g hP hKP
      (QuotientGroup.mk' _ y) = _
    rw [Work.Shrinking.quotAut_mk]
  have keyQ : g • (QuotientGroup.mk'
        ((flowTerm p G n i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)))
        ⟨Φ.toHom (y : Work.Shrinking.freeOperatorGroup G m), Subgroup.mem_top _⟩)
      = QuotientGroup.mk'
        ((flowTerm p G n i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)))
        (Work.Shrinking.subAut ⊤ g hQ
          ⟨Φ.toHom (y : Work.Shrinking.freeOperatorGroup G m), Subgroup.mem_top _⟩) := by
    change Work.Shrinking.quotAut ⊤ (flowTerm p G n i j) g hQ hKQ
      (QuotientGroup.mk' _ _) = _
    rw [Work.Shrinking.quotAut_mk]
  rw [keyP]
  simp only [flowQuotMap_mk]
  rw [keyQ]
  congr 1
  refine Subtype.ext ?_
  simp only [Work.Shrinking.subAut_coe]
  exact Φ.equivariant g (y : Work.Shrinking.freeOperatorGroup G m)

end Work.CohomologicalShrinking.flow
