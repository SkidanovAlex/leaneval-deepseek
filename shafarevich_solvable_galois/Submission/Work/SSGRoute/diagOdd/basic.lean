import Mathlib
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.kerSucc_conj_eq_mk_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Basic interface for the graded quotient `Q_{(j+1,1)} = F(n)/P_{j+1}`

Clash-free copies of the elementary facts about `flowQuotient` and `flowAction` that live in
`gradedStep_diagonal` (which is under construction elsewhere in the workspace).
-/

noncomputable section

open Work.CohomologicalShrinking

namespace Work.SSGRoute.diagOdd

universe u

variable {G : Type u} [Group G] {n : ℕ}

/-- The permutation `(i, g) ↦ (i, δ * g)` of the basis of the free operator group. -/
abbrev basisPerm (G : Type u) [Group G] (n : ℕ) (δ : G) : (Fin n × G) ≃ (Fin n × G) :=
  Work.Shrinking.freeOperatorGenPerm (G := G) n δ

theorem basisPerm_apply (δ : G) (x : Fin n × G) :
    basisPerm G n δ x = (x.1, δ * x.2) := rfl

theorem basisPerm_involutive (δ : G) (hδ : δ * δ = 1) (x : Fin n × G) :
    basisPerm G n δ (basisPerm G n δ x) = x := by
  show (x.1, δ * (δ * x.2)) = x
  rw [← mul_assoc, hδ, one_mul]

theorem basisPerm_ne_self (δ : G) (hδ1 : δ ≠ 1) (x : Fin n × G) :
    basisPerm G n δ x ≠ x := by
  intro h
  have h2 : δ * x.2 = x.2 := by
    simpa [basisPerm, Work.Shrinking.freeOperatorGenPerm] using congrArg Prod.snd h
  exact hδ1 (mul_right_cancel (by rw [h2, one_mul]))

theorem smul_eq_freeGroupCongr (δ : G) (x : Work.Shrinking.freeOperatorGroup G n) :
    δ • x = FreeGroup.freeGroupCongr (basisPerm G n δ) x := rfl

@[simp]
theorem flowQuotSucc_mk (p : ℕ) (m i j : ℕ)
    (x : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
    Work.SSGRoute.flowQuotSucc p G m i j (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x :=
  QuotientGroup.map_mk' _ _ _ _ x

/-- The class of the `δ`-image is the `δ`-image of the class. -/
theorem flowAction_mk_top (δ : G) (j : ℕ)
    (y : Work.Shrinking.freeOperatorGroup G n) :
    (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
        (QuotientGroup.mk'
          ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
          ⟨y, Subgroup.mem_top y⟩)
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨δ • y, Subgroup.mem_top _⟩ := by
  have hP : Subgroup.map (MulDistribMulAction.toMulAut G
      (Work.Shrinking.freeOperatorGroup G n) δ).toMonoidHom
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)) = ⊤ :=
    Subgroup.map_top_of_surjective _
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) δ).surjective
  have hK : Subgroup.map (MulDistribMulAction.toMulAut G
      (Work.Shrinking.freeOperatorGroup G n) δ).toMonoidHom
      (flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2 :=
    Work.CohomologicalShrinking.map_refinedTerm_eq 2 _ (tauSucc j j).1 (tauSucc j j).2
  change Work.Shrinking.quotAut ⊤ (flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2) δ hP hK
    (QuotientGroup.mk'
      ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤) ⟨y, Subgroup.mem_top y⟩)
    = _
  rw [Work.Shrinking.quotAut_mk]
  exact congrArg (QuotientGroup.mk'
      ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤))
    (Subtype.ext (by simp [Work.Shrinking.subAut_coe]))

theorem refinedTerm_eq_sup (j : ℕ) :
    flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2
      = Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) j := by
  rw [tauSucc_of_le (le_refl j)]
  exact Work.CohomologicalShrinking.refinedTerm_one 2 _ (j + 1)

end Work.SSGRoute.diagOdd
