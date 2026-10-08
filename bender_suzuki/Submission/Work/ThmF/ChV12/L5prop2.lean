import Mathlib
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.prop2v2
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L5prop2` — `K = J(D,t)` is a subgroup (Peterfalvi II Ch. V §1 Prop. 2)
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV12

/-- Case `V = C_D(t) = 1`: then `|K| = |D|` by App. I (1)(b), and `K ⊆ D`, so `K = D`
is a subgroup. -/
private theorem Ksub_eq_Kset_of_centD_bot {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t s : G} (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hV : centD H t = ⊥) : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := by
  have hsplit : IsSplitRankOne H Q t := h.split
  have hcard := Work.ThmF.card_centD_mul_card_Kset (H := H) (t := t)
    (Work.ThmF.IsSplitRankOne.toData hsplit)
  rw [hV, Subgroup.card_bot, one_mul] at hcard
  have hKD : Work.ThmF.Kset H t ⊆ (twoPoint H t : Set G) := Work.ThmF.Kset_subset H t
  have hDcard : (twoPoint H t : Set G).ncard = (Work.ThmF.Kset H t).ncard := by
    rw [← Nat.card_coe_set_eq]; exact hcard.symm
  have hKeq : Work.ThmF.Kset H t = (twoPoint H t : Set G) :=
    Set.eq_of_subset_of_ncard_le hKD (le_of_eq hDcard)
  rw [Work.ThmF.Ksub, hKeq, Subgroup.closure_eq]

/-- Case `W = C_V(K) ≠ 1`: take `X = W`; all of `K` centralises `X`, so clause P3 of
`ChIIFourProp` returns a cyclic `N = K ∩ N_G(X) = K`, whence `K` is a subgroup. -/
private theorem Ksub_eq_Kset_of_W_ne_bot {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t s : G} (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hW : Work.ThmF.W H t ≠ ⊥) : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := by
  have hsplit : IsSplitRankOne H Q t := h.split
  have hP3 := (hC4 G h.sit H hsplit.stronglyEmbedded t hsplit.invol hsplit.not_mem).2.2.2.1
  obtain ⟨k0, hk0, hk01⟩ := Work.ThmF.L5.exists_mem_Kset_ne_one h.sit hsplit
  -- every element of `K` normalises `W` (it centralises it)
  have hKN : Work.ThmF.Kset H t ⊆ (Subgroup.normalizer (Work.ThmF.W H t : Set G) : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro x
    constructor
    · intro hx
      have hxcent : x ∈ Subgroup.centralizer (Work.ThmF.Kset H t : Set G) :=
        (Subgroup.mem_inf.mp hx).2
      have hcx : k * x = x * k := Subgroup.mem_centralizer_iff.mp hxcent k hk
      have : k * x * k⁻¹ = x := by rw [hcx]; group
      rw [this]; exact hx
    · intro hx
      have hxcent : k * x * k⁻¹ ∈ Subgroup.centralizer (Work.ThmF.Kset H t : Set G) :=
        (Subgroup.mem_inf.mp hx).2
      have hki : k⁻¹ ∈ Work.ThmF.Kset H t := Work.ThmF.L5.Kset_inv_mem h hk
      have hcomm : (k * x * k⁻¹) * k⁻¹ = k⁻¹ * (k * x * k⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hxcent k⁻¹ hki).symm
      have hxe : x = k * x * k⁻¹ := by
        calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
          _ = ((k * x * k⁻¹) * k⁻¹) * k := by rw [hcomm]
          _ = k * x * k⁻¹ := by group
      rw [hxe]; exact hx
  obtain ⟨-, -, -, hN⟩ := hP3 (Work.ThmF.W H t) hW (Work.ThmF.W_le_centD H t)
    ⟨k0, hk0, hk01, hKN hk0⟩
  obtain ⟨N, hNset, -, hNcyc⟩ := hN
  have hNset' : (N : Set G) = Work.ThmF.Kset H t := by
    rw [hNset]
    exact Set.Subset.antisymm Set.inter_subset_left (fun x hx => ⟨hx, hKN hx⟩)
  have hKsub_eq : Work.ThmF.Ksub H t = N := by
    refine le_antisymm ?_ ?_
    · show Subgroup.closure (Work.ThmF.Kset H t) ≤ N
      refine (Subgroup.closure_le N).mpr ?_
      intro x hx
      rw [hNset']; exact hx
    · intro x hx
      exact Work.ThmF.Kset_le_Ksub H t (by rw [← hNset']; exact hx)
  rw [hKsub_eq, hNset']

/-- **`K = J(D,t)` is a subgroup** (Peterfalvi II Ch. V §1 Prop. 2), for `Hyp5` data.  The
odd order theorem is needed only through Appendix X (`Work.ThmF.Tools.appX`), see
`Work.ThmF.ChV12.Ksub_cyclic_normal`. -/
theorem L5prop2 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G} (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
  (Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 h.sit h.split).2.1

end Work.ThmF.ChV12
