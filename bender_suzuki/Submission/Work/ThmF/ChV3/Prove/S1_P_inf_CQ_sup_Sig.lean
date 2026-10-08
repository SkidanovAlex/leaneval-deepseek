import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.S1_P_inf_CQ_sup_Sig`

Step (1) of §3: the prime-order subgroup `P ≤ V = C_D(t)` meets `C_Q(P) · Σ` trivially, where
`Σ = C_W(P)` and `C_Q(P) = Q ∩ C_G(P)`.

Two structural facts drive the proof.

* `Σ ≤ N_G(C_Q(P))`: `Σ ≤ W ≤ V ≤ D ≤ H`, and `H` normalises `Q`, so `Σ` normalises `Q` by
  conjugation; moreover `Σ`, `C_Q(P) ≤ C_G(P)`, and `C_G(P)` is a subgroup, so the conjugate
  again centralises `P`.  Hence `C_Q(P) ⊔ Σ = C_Q(P) · Σ` and every element of the join factors.

* `Q ∩ D = ⊥` (split rank one data) and `W ∩ P = ⊥` (step (1), `h15.hWP`).

Indeed, if `x = c · σ` with `c ∈ C_Q(P) ≤ Q` and `σ ∈ Σ ≤ D` lies in `P ≤ V ≤ D`, then
`c = x · σ⁻¹ ∈ D ∩ Q = ⊥`, so `c = 1` and `x = σ ∈ Σ ∩ P ≤ W ∩ P = ⊥`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint
open Pointwise

namespace Work.ThmF.ChV3.Prove

theorem S1_P_inf_CQ_sup_Sig {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P) :
    P ⊓ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) = ⊥ := by
  -- ## The three containments placing `Σ = C_W(P)` inside `V ≤ D ≤ H` and in `C_G(P)`
  have hSig_le_W : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t := inf_le_left
  have hSig_le_centD : Work.ThmF.ChV3.Sig H t P ≤ centD H t :=
    hSig_le_W.trans (Work.ThmF.W_le_centD H t)
  have hSig_le_D : Work.ThmF.ChV3.Sig H t P ≤ twoPoint H t :=
    hSig_le_centD.trans (Work.ThmF.centD_le_twoPoint t)
  have hSig_le_H : Work.ThmF.ChV3.Sig H t P ≤ H := hSig_le_D.trans inf_le_left
  have hP_le_D : P ≤ twoPoint H t := c.P_le.trans (Work.ThmF.centD_le_twoPoint t)
  -- ## `x ∈ Σ` centralises `P`; `x ∈ C_Q(P)` lies in `Q` and centralises `P`
  have hSig_mem_C : ∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ∈ Subgroup.centralizer (P : Set G) :=
    fun _ hσ => (Subgroup.mem_inf.mp hσ).2
  have hCQ_mem_Q : ∀ c' ∈ Work.ThmF.ChV3.CQ Q P, c' ∈ Q :=
    fun _ hc => (Subgroup.mem_inf.mp hc).1
  have hCQ_mem_C : ∀ c' ∈ Work.ThmF.ChV3.CQ Q P, c' ∈ Subgroup.centralizer (P : Set G) :=
    fun _ hc => (Subgroup.mem_inf.mp hc).2
  -- ## `Σ` normalises `C_Q(P)`, so the join is the product set `C_Q(P) · Σ`
  have hSig_le_N : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.normalizer (Work.ThmF.ChV3.CQ Q P : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro σ hσ c' hc'
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.le_normalizer_iff.mp c.split.normal) σ (hSig_le_H hσ) c' (hCQ_mem_Q c' hc')
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hSig_mem_C σ hσ) (hCQ_mem_C c' hc'))
        (Subgroup.inv_mem _ (hSig_mem_C σ hσ))
  -- ## the intersection is trivial
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxP, hxU⟩ := Subgroup.mem_inf.mp hx
  have hxU' : x ∈ (Work.ThmF.ChV3.CQ Q P : Set G) * (Work.ThmF.ChV3.Sig H t P : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Work.ThmF.ChV3.CQ Q P)
      (Work.ThmF.ChV3.Sig H t P) hSig_le_N]
    exact hxU
  rw [Set.mem_mul] at hxU'
  obtain ⟨c', hc', σ, hσ, hc'σ⟩ := hxU'
  -- `c' = x · σ⁻¹ ∈ D` because `x ∈ P ≤ D` and `σ ∈ Σ ≤ D`
  have hc'D : c' ∈ twoPoint H t := by
    have : c' = x * σ⁻¹ := by rw [← hc'σ]; group
    rw [this]
    exact (twoPoint H t).mul_mem (hP_le_D hxP) ((twoPoint H t).inv_mem (hSig_le_D hσ))
  -- ... while `c' ∈ Q`, and `Q ∩ D = ⊥`
  have hc'1 : c' = 1 := by
    have hmem : c' ∈ Q ⊓ twoPoint H t := ⟨hCQ_mem_Q c' hc', hc'D⟩
    rw [Work.ThmF.split_inf_eq c.split] at hmem
    exact Subgroup.mem_bot.mp hmem
  -- hence `x = σ ∈ Σ ≤ W`, and `x ∈ P`, so `x ∈ W ∩ P = ⊥`
  have hxW : x ∈ Work.ThmF.W H t := by
    have hσx : σ = x := by rw [← hc'σ, hc'1, one_mul]
    exact hσx ▸ hSig_le_W hσ
  have hmem : x ∈ Work.ThmF.W H t ⊓ P := ⟨hxW, hxP⟩
  rw [h15.hWP] at hmem
  exact Subgroup.mem_bot.mp hmem

end Work.ThmF.ChV3.Prove
