import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.S1_CH_aux`

Auxiliary facts feeding the cardinality computation `|C_H(P)| = |C_Q(P)| |Σ| |P|` for step (1) of
Peterfalvi II Ch. V §3 (`S1_CH_card`): with `C_Q(P) = Q ⊓ C_G(P)` and `Σ = C_W(P) = W ⊓ C_G(P)`,

* `Σ ⊔ P ≤ N_G(C_Q(P))` (so the join is a subgroup product),
* `C_Q(P) ⊓ (Σ ⊔ P) = ⊥`,
* `Σ ⊓ P = ⊥`.

The last two are immediate from the split rank-one structure: `Σ ⊔ P ≤ W ⊔ P = V ≤ D = H ⊓ Hᵗ`
(`h15.hV`) while `C_Q(P) ≤ Q` and `Q ⊓ D = ⊥`, and `Σ ≤ W` while `W ⊓ P = ⊥` (`h15.hWP`).

For the normaliser claim: `Σ ≤ W ≤ D ≤ H` normalises `Q` and lies in `C_G(P)`, as does
`C_Q(P)`, so conjugation stays inside `C_Q(P)`; `P ≤ V ≤ D ≤ H` normalises `Q` as well, and for
`x ∈ P`, `c ∈ C_Q(P)`, `p ∈ P` one has `x c x⁻¹ p x c⁻¹ x⁻¹ = x (c (x⁻¹ p x) c⁻¹) x⁻¹ = p`
because `c` centralises `x⁻¹ p x ∈ P`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3.Prove

theorem S1_CH_aux {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P) :
    Work.ThmF.ChV3.Sig H t P ⊔ P ≤ Subgroup.normalizer (Work.ThmF.ChV3.CQ Q P : Set G) ∧
      Work.ThmF.ChV3.CQ Q P ⊓ (Work.ThmF.ChV3.Sig H t P ⊔ P) = ⊥ ∧
      Work.ThmF.ChV3.Sig H t P ⊓ P = ⊥ := by
  have hSig_le_W : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t := inf_le_left
  have hSig_le_centD : Work.ThmF.ChV3.Sig H t P ≤ centD H t :=
    hSig_le_W.trans (Work.ThmF.W_le_centD H t)
  have hSig_le_H : Work.ThmF.ChV3.Sig H t P ≤ H :=
    hSig_le_centD.trans ((Work.ThmF.centD_le_twoPoint t).trans inf_le_left)
  have hP_le_D : P ≤ twoPoint H t := c.P_le.trans (Work.ThmF.centD_le_twoPoint t)
  have hP_le_H : P ≤ H := hP_le_D.trans inf_le_left
  have hSig_mem_C : ∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ∈ Subgroup.centralizer (P : Set G) :=
    fun _ hσ => (Subgroup.mem_inf.mp hσ).2
  have hCQ_mem_Q : ∀ c' ∈ Work.ThmF.ChV3.CQ Q P, c' ∈ Q := fun _ hc => (Subgroup.mem_inf.mp hc).1
  have hCQ_mem_C : ∀ c' ∈ Work.ThmF.ChV3.CQ Q P, c' ∈ Subgroup.centralizer (P : Set G) :=
    fun _ hc => (Subgroup.mem_inf.mp hc).2
  refine ⟨?_, ?_, ?_⟩
  · -- ## `Σ ⊔ P ≤ N_G(C_Q(P))`
    refine sup_le ?_ ?_
    · -- `Σ` normalises `C_Q(P)`: it lies in `H` (hence normalises `Q`) and in `C_G(P)`
      rw [Subgroup.le_normalizer_iff]
      intro σ hσ c' hc'
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.le_normalizer_iff.mp c.split.normal) σ (hSig_le_H hσ) c' (hCQ_mem_Q c' hc')
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hSig_mem_C σ hσ) (hCQ_mem_C c' hc'))
          (Subgroup.inv_mem _ (hSig_mem_C σ hσ))
    · -- `P` normalises `C_Q(P)`: `P ≤ H` normalises `Q`, and `P` normalises `C_G(P)`
      -- because `C_Q(P)` centralises `P` (here `x⁻¹ p x ∈ P`)
      rw [Subgroup.le_normalizer_iff]
      intro x hx c' hc'
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.le_normalizer_iff.mp c.split.normal) x (hP_le_H hx) c' (hCQ_mem_Q c' hc')
      · rw [Subgroup.mem_centralizer_iff]
        intro p hp
        have hcomm := (Subgroup.mem_centralizer_iff.mp (hCQ_mem_C c' hc')) (x⁻¹ * p * x)
          (P.mul_mem (P.mul_mem (P.inv_mem hx) hp) hx)
        calc p * (x * c' * x⁻¹)
            = x * ((x⁻¹ * p * x) * c') * x⁻¹ := by group
          _ = x * (c' * (x⁻¹ * p * x)) * x⁻¹ := by rw [hcomm]
          _ = x * c' * x⁻¹ * p := by group
  · -- ## `C_Q(P) ⊓ (Σ ⊔ P) = ⊥`: the join lies in `V ≤ D` while `C_Q(P) ≤ Q`, and `Q ⊓ D = ⊥`
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzCQ, hzSP⟩ := Subgroup.mem_inf.mp hz
    have hzQ : z ∈ Q := (Subgroup.mem_inf.mp hzCQ).1
    have hzD : z ∈ twoPoint H t :=
      (sup_le hSig_le_centD c.P_le).trans (Work.ThmF.centD_le_twoPoint t) hzSP
    have hmem : z ∈ Q ⊓ twoPoint H t := ⟨hzQ, hzD⟩
    rw [c.split.inf_eq] at hmem
    exact Subgroup.mem_bot.mp hmem
  · -- ## `Σ ⊓ P = ⊥`: `Σ ≤ W` and `W ⊓ P = ⊥`
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzSig, hzP⟩ := Subgroup.mem_inf.mp hz
    have hmem : z ∈ Work.ThmF.W H t ⊓ P := ⟨hSig_le_W hzSig, hzP⟩
    rw [h15.hWP] at hmem
    exact Subgroup.mem_bot.mp hmem

end Work.ThmF.ChV3.Prove
