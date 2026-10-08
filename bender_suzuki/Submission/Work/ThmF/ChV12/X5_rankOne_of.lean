import Mathlib
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.ChV12.X5RankOneAux
import Submission.Work.ThmF.ChV12.L5oddKsub
import Submission.Work.ThmF.ChV12.L5simpleX5

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-! ## Two elementary facts about conjugation of subgroups -/

/-- Conjugation by an element of a subgroup leaves that subgroup unchanged. -/
theorem bp_conj_eq_of_mem {A : Subgroup G} {a : G} (ha : a ∈ A) :
    Submission.Blueprint.conj a A = A := by
  ext y
  rw [Work.Models.mem_conj_iff]
  constructor
  · intro hy
    have h : y = a * (a⁻¹ * y * a) * a⁻¹ := by group
    rw [h]
    exact A.mul_mem (A.mul_mem ha hy) (A.inv_mem ha)
  · intro hy
    exact A.mul_mem (A.mul_mem (A.inv_mem ha) hy) ha

/-- Conjugation distributes over intersection of subgroups. -/
theorem bp_conj_inf (a : G) (A B : Subgroup G) :
    Submission.Blueprint.conj a (A ⊓ B)
      = Submission.Blueprint.conj a A ⊓ Submission.Blueprint.conj a B :=
  Subgroup.map_inf A B (MulAut.conj a).toMonoidHom (MulAut.conj a).injective

/-! ## `B = Q₀K` is strongly embedded in `X = ⟨Q₀,K,t⟩` -/

/-- `B ⊓ B^g` for `g ∉ B` inside `X` is a conjugate of `K`, hence of odd order. -/
theorem bor_odd_card_twoPoint (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (g : ↥(Work.ThmF.Lemma5.X5 H t))
    (hg : g ∉ (Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :
    Odd (Nat.card
      (twoPoint ((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) g)) := by
  set M := (Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) with hM
  have hg0 : (g : G) ∉ Work.ThmF.L5.bor H t :=
    fun hc => hg (Subgroup.mem_subgroupOf.mpr hc)
  rcases Work.ThmF.L5.mem_bor_or_btb hC4 h g.2 with hb | ⟨b₁, hb₁, b₂, hb₂, hge⟩
  · exact absurd hb hg0
  · have hconjle : Submission.Blueprint.conj (g : G) (Work.ThmF.L5.bor H t)
        ≤ Work.ThmF.Lemma5.X5 H t := by
      intro y hy
      rw [Work.Models.mem_conj_iff] at hy
      have h : y = (g : G) * ((g : G)⁻¹ * y * (g : G)) * (g : G)⁻¹ := by group
      rw [h]
      exact (Work.ThmF.Lemma5.X5 H t).mul_mem
        ((Work.ThmF.Lemma5.X5 H t).mul_mem g.2 (Work.ThmF.L5.bor_le_X5 hy))
        ((Work.ThmF.Lemma5.X5 H t).inv_mem g.2)
    have hle : Work.ThmF.L5.bor H t ⊓ Submission.Blueprint.conj (g : G) (Work.ThmF.L5.bor H t)
        ≤ Work.ThmF.Lemma5.X5 H t := le_trans inf_le_left Work.ThmF.L5.bor_le_X5
    have hB : Work.ThmF.L5.bor H t ⊓ Submission.Blueprint.conj (g : G) (Work.ThmF.L5.bor H t)
        = Submission.Blueprint.conj b₁ (Work.ThmF.Ksub H t) := by
      have step1 : Submission.Blueprint.conj (g : G) (Work.ThmF.L5.bor H t)
          = Submission.Blueprint.conj b₁
              (Submission.Blueprint.conj t (Work.ThmF.L5.bor H t)) := by
        rw [hge, Work.Models.conj_mul (b₁ * t) b₂ (Work.ThmF.L5.bor H t),
          bp_conj_eq_of_mem hb₂, Work.Models.conj_mul b₁ t (Work.ThmF.L5.bor H t)]
      rw [step1, ← Work.ThmF.L5.twoPoint_bor_eq_Ksub hC4 h,
        bp_conj_inf b₁ (Work.ThmF.L5.bor H t)
          (Submission.Blueprint.conj t (Work.ThmF.L5.bor H t)),
        bp_conj_eq_of_mem hb₁]
    have htwo : twoPoint M g = (Work.ThmF.L5.bor H t ⊓
        Submission.Blueprint.conj (g : G) (Work.ThmF.L5.bor H t)).subgroupOf
        (Work.ThmF.Lemma5.X5 H t) := by
      show M ⊓ Submission.Blueprint.conj g M = _
      rw [hM, Work.ThmF.L5.conj_subgroupOf g.2 (Work.ThmF.L5.bor H t),
        ← Work.ThmF.L5.subgroupOf_inf_eq]
    rw [htwo, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hB,
      Subgroup.card_map_of_injective (f := (MulAut.conj b₁).toMonoidHom)
        (MulAut.conj b₁).injective]
    exact Work.ThmF.ChV12.L5oddKsub h

/-- `B = Q₀sub H ⊔ Ksub H t` is strongly embedded in `X = X5 H t`. -/
theorem bor_stronglyEmbedded (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    IsStronglyEmbedded ((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) := by
  refine ⟨Work.ThmF.L5.bor_subgroupOf_ne_top h, ?_, ?_⟩
  · have hcard : Nat.card ↥((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t))
        = Nat.card ↥(Work.ThmF.L5.bor H t) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Work.ThmF.L5.bor_le_X5 (H := H) (t := t))).toEquiv
    rw [hcard]
    exact Work.ThmF.L5.even_card_bor h
  · intro g hg
    exact bor_odd_card_twoPoint hC4 h g hg

/-! ## The assembly -/

theorem X5_rankOne_of {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    IsSimpleGroup ↥(Work.ThmF.Lemma5.X5 H t) ∧
      Submission.Blueprint.IsSplitRankOne
        ((Work.ThmF.Q0sub H ⊔ Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Lemma5.X5 H t))
        ((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t)) (Work.ThmF.Lemma5.tX H t) ∧
      ∀ k ∈ Work.ThmF.Kset H t, ∃ m ∈ Work.ThmF.Q0sub H ⊔ Work.ThmF.Ksub H t,
        t * (k⁻¹ * s * k) * t = m * t * (k * s * k⁻¹) := by
  refine ⟨Work.ThmF.ChV12.L5simpleX5 hC4 h, ?_, ?_⟩
  · refine ⟨bor_stronglyEmbedded hC4 h, Work.ThmF.ChV12.X5_twoTransitive hC4 h,
      Work.ThmF.L5.orderOf_tX h, Work.ThmF.L5.tX_notMem_bor h, ?_, ?_, ?_, ?_⟩
    · exact Subgroup.subgroupOf_mono (Work.ThmF.Lemma5.X5 H t)
        (le_sup_left : (Work.ThmF.Q0sub H : Subgroup G) ≤
          Work.ThmF.Q0sub H ⊔ Work.ThmF.Ksub H t)
    · exact Work.ThmF.L5.subgroupOf_bor_le_normalizer_subgroupOf hC4 h
    · rw [Work.ThmF.L5.twoPoint_bor_subgroupOf hC4 h, ← Work.ThmF.L5.subgroupOf_inf_eq,
        Work.ThmF.L5.Q0sub_inf_Ksub_eq_bot h]
      ext y
      simp [Subgroup.mem_subgroupOf]
    · rw [Work.ThmF.L5.twoPoint_bor_subgroupOf hC4 h, ← Subgroup.subgroupOf_sup
          (Work.ThmF.L5.Q0sub_le_X5 (H := H) (t := t))
          (Work.ThmF.L5.Ksub_le_X5 (H := H) (t := t))]
  · intro k hk
    exact Work.ThmF.L5.f_relation h k hk

end Work.ThmF.ChV12
