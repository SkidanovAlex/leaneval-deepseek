import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.CohomologicalShrinking.Functorial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.functorial

open Work.CohomologicalShrinking

theorem gradedMapAdd_smul (p : ℕ) {G P Q : Type*} [Group G] [Group P] [Group Q]
    [MulDistribMulAction G P] [MulDistribMulAction G Q]
    (ψ : P →* Q) (hψ : Function.Surjective ψ)
    (hψG : ∀ (g : G) (x : P), ψ (g • x) = g • ψ x) (i j : ℕ) (g : G)
    (z : Additive (refinedQuotient p P i j)) :
    gradedMapAdd p ψ hψ i j (g • z) = g • gradedMapAdd p ψ hψ i j z := by
  have hmul : ∀ x : refinedQuotient p P i j,
      gradedMapMul p ψ hψ i j (g • x) = g • gradedMapMul p ψ hψ i j x := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      ((refinedTerm p P (tauSucc i j).1 (tauSucc i j).2).subgroupOf (refinedTerm p P i j)) x
    have keyP : g • (QuotientGroup.mk'
          ((refinedTerm p P (tauSucc i j).1 (tauSucc i j).2).subgroupOf (refinedTerm p P i j)) y)
        = QuotientGroup.mk'
          ((refinedTerm p P (tauSucc i j).1 (tauSucc i j).2).subgroupOf (refinedTerm p P i j))
          (Work.Shrinking.subAut (refinedTerm p P i j) g
            (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G P g) i j) y) := by
      change Work.Shrinking.quotAut (refinedTerm p P i j)
          (refinedTerm p P (tauSucc i j).1 (tauSucc i j).2) g
          (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G P g) i j)
          (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G P g) (tauSucc i j).1 (tauSucc i j).2)
          (QuotientGroup.mk'
            ((refinedTerm p P (tauSucc i j).1 (tauSucc i j).2).subgroupOf (refinedTerm p P i j)) y) = _
      rw [Work.Shrinking.quotAut_mk]
    have keyQ : g • (QuotientGroup.mk'
          ((refinedTerm p Q (tauSucc i j).1 (tauSucc i j).2).subgroupOf (refinedTerm p Q i j))
          (refinedMap p ψ hψ i j y))
        = QuotientGroup.mk'
          ((refinedTerm p Q (tauSucc i j).1 (tauSucc i j).2).subgroupOf (refinedTerm p Q i j))
          (Work.Shrinking.subAut (refinedTerm p Q i j) g
            (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G Q g) i j)
            (refinedMap p ψ hψ i j y)) := by
      change Work.Shrinking.quotAut (refinedTerm p Q i j)
          (refinedTerm p Q (tauSucc i j).1 (tauSucc i j).2) g
          (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G Q g) i j)
          (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G Q g) (tauSucc i j).1 (tauSucc i j).2)
          (QuotientGroup.mk' _ (refinedMap p ψ hψ i j y)) = _
      rw [Work.Shrinking.quotAut_mk]
    rw [keyP]
    simp only [gradedMapMul_of]
    rw [keyQ]
    congr 1
    refine Subtype.ext ?_
    rw [refinedMap_coe, Work.Shrinking.subAut_coe, Work.Shrinking.subAut_coe, refinedMap_coe]
    exact hψG g (y : P)
  show Additive.ofMul (gradedMapMul p ψ hψ i j (g • Additive.toMul z)) =
    Additive.ofMul (g • gradedMapMul p ψ hψ i j (Additive.toMul z))
  exact congrArg Additive.ofMul (hmul (Additive.toMul z))

end Work.CohomologicalShrinking.functorial
