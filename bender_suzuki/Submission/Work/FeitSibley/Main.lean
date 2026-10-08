import Submission.Work.FeitSibley.CharQ.Defs
import Submission.Work.FeitSibley.CharQ.two_le_card_scriptS
import Submission.Work.FeitSibley.Coherence.coherent_scriptS

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley`: from the Feit–Sibley set-up to `FeitSibleyProp`

This module assembles the target: `Submission.Blueprint.FeitSibleyProp` follows from the
Feit–Sibley hypotheses (`FSData`) together with the two conclusions of Peterfalvi II,
Appendice XII:

* `2 ≤ |𝒮|` (the cardinality of `𝒮 = {χ ∈ Irr H | Q₁ ⊄ ker χ}`), proved in
  `CharQ/two_le_card_scriptS.lean`;
* coherence of `𝒮` for `Ind_H^G`, the content of the appendix (Lemma 2 is
  `CharQ/scriptS_eq_image.lean` + `CharQ/isometry_indLin.lean`; the theorem itself is
  `Coherence/…`).

Because the appendix's coherence theorem is stated here as an explicit hypothesis, the final
unconditional theorem is `feitSibley_of_coherence`.
-/

noncomputable section

open Classical

namespace Work.FeitSibley

open Submission.Blueprint

/-- The `FSData` assembled from the eighteen hypotheses of `FeitSibleyProp`. -/
def FSData.ofHyp {G : Type} [Group G] [Fintype G] (H Q D S Q1 : Subgroup G)
    (H_ne_top : H ≠ ⊤) (Q_le_H : Q ≤ H) (Q_normal_in_H : H ≤ Subgroup.normalizer (Q : Set G))
    (D_le_H : D ≤ H) (Q_inf_D : Q ⊓ D = ⊥) (Q_sup_D : Q ⊔ D = H)
    (coprime_D_Q : Nat.Coprime (Nat.card D) (Nat.card Q))
    (Q_TI : ∀ x : G, x ∉ H → Q ⊓ Submission.Blueprint.conj x Q = ⊥)
    (S_sup_Q1 : S ⊔ Q1 = Q) (S_inf_Q1 : S ⊓ Q1 = ⊥)
    (commute : ∀ a ∈ S, ∀ b ∈ Q1, a * b = b * a)
    (coprime_S_Q1 : Nat.Coprime (Nat.card S) (Nat.card Q1))
    (S_nilpotent : Group.IsNilpotent S)
    (D_fpf_Q1 : ∀ d ∈ D, d ≠ 1 → ∀ x ∈ Q1, d * x * d⁻¹ = x → x = 1)
    (Q1_not_two : ¬ IsPGroup 2 Q1) (D_odd : Odd (Nat.card D)) : FSData G :=
  { H := H, Q := Q, D := D, S := S, Q1 := Q1
    H_ne_top := H_ne_top, Q_le_H := Q_le_H, Q_normal_in_H := Q_normal_in_H, D_le_H := D_le_H
    Q_inf_D := Q_inf_D, Q_sup_D := Q_sup_D, coprime_D_Q := coprime_D_Q, Q_TI := Q_TI
    S_sup_Q1 := S_sup_Q1, S_inf_Q1 := S_inf_Q1, commute := commute
    coprime_S_Q1 := coprime_S_Q1, S_nilpotent := S_nilpotent, D_fpf_Q1 := D_fpf_Q1
    Q1_not_two := Q1_not_two, D_odd := D_odd }

/-- **Feit–Sibley** (`FeitSibleyProp`) from the two conclusions of Peterfalvi II, App. XII:
the cardinality of `𝒮` and its coherence for `Ind_H^G`.  `hFT` is carried for the shape of the
area theorem (App. XII does not use the odd order theorem). -/
theorem feitSibley_of_coherence (hFT : FeitThompsonProp)
    (hcard : ∀ (G : Type) [Group G] [Fintype G] (h : FSData G),
      2 ≤ (scriptS h.H h.Q1).card)
    (hcoh : ∀ (G : Type) [Group G] [Fintype G] (h : FSData G),
      Work.Coherence.Coherent (scriptS h.H h.Q1) (indLin h.H)) :
    FeitSibleyProp := by
  intro G _ _ H Q D S Q1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  refine ⟨?_, ?_⟩
  · exact hcard G (FSData.ofHyp H Q D S Q1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)
  · exact hcoh G (FSData.ofHyp H Q D S Q1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)

/-- **Feit–Sibley** (`FeitSibleyProp`) from the coherence theorem alone: the cardinality
`2 ≤ |𝒮|` is `Work.FeitSibley.CharQ.two_le_card_scriptS`. -/
theorem feitSibley_of_scriptS_coherent (hFT : FeitThompsonProp)
    (hcoh : ∀ (G : Type) [Group G] [Fintype G] (h : FSData G),
      Work.Coherence.Coherent (scriptS h.H h.Q1) (indLin h.H)) :
    FeitSibleyProp :=
  feitSibley_of_coherence hFT
    (fun G _ _ h => Work.FeitSibley.CharQ.two_le_card_scriptS h) hcoh

/-- **The Feit–Sibley theorem** (Peterfalvi II, Appendice XII, Théorème p. 289), i.e.
`Submission.Blueprint.FeitSibleyProp`, from the odd order theorem `hFT` (carried for the shape of
the area theorem: App. XII does not use it). -/
theorem feitSibley (hFT : FeitThompsonProp) : FeitSibleyProp :=
  feitSibley_of_scriptS_coherent hFT
    (fun G _ _ h => Work.FeitSibley.Coherence.coherent_scriptS h)

end Work.FeitSibley
