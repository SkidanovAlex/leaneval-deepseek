import Submission.Work.CORE2B.Deliverable
import Submission.Work.CORE2B.L27_v12_assembly
import Submission.Work.CORE2B.L27su_fittingPiIn_compl_ne_bot
import Submission.Work.CORE2B.L27_fourGroup_in_C_M_t
import Submission.Work.CORE2B.L27su_transport
import Submission.Work.CORE2B.L27_su_not_le_h22_proved

/-!
# AREA CORE2B — Lemma 2.7(b), and the completed contract `Lemma27Prop`

The colleague who reduced Bender's Lemma 2.7(b) (`[S,U] ⊄ F(U)`) left
`L27su_of_gaps : (three inputs) → L27_su_not_le_h22` (`Submission.Work.CORE2B.L27_su_not_le_h22_proved`),
with the three inputs being

* `F_{π'}(M) ≠ ⊥` (`L27su_fittingPiIn_compl_ne_bot` — proved),
* a four-group `V ≤ M ⊓ C(t)` with `t ∈ V` (`L27_fourGroup_in_C_M_t` — proved),
* the transport step (`L27su_transport` — proved).

This file feeds them in, and then assembles the contract statement `Lemma27Prop` from the three
conclusions of Lemma 2.7 — all three of which are now proved in the area
(`L27_commutator_le_v12`, `L27_su_not_le_h22_v12`, `L27_solvable_v12`).
-/

open scoped MatrixGroups commutatorElement

set_option linter.unusedVariables false

namespace Work.CORE2B

open Subgroup

/-- The first of the three gaps of `L27su_of_gaps`, `F_{π'}(M) ≠ ⊥`, re-proved from the now
available conclusion (a): if `F_{π'}(M)` were trivial then `[M,t] = ⊥`, so `t` would centralize
`M`, giving `M ≤ H ≤ Ĥ` and contradicting `¬ M ≤ Ĥ`. -/
theorem L27su_A_ne_bot_v12 :
    ∀ (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop) (h23 : Work.GW2.Lemma23Prop)
      (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M →
        Work.GW2.fittingPiIn B.piᶜ M ≠ ⊥ := by
  intro T h22 h23 h26 G _ _ hFT hCtx B M hD hbot
  have hcomm := L27_commutator_le_v12 T h23 h26 G hFT hCtx B M hD
  have hMt : ⁅M, Subgroup.zpowers B.t⁆ = ⊥ := le_bot_iff.mp (hbot ▸ hcomm)
  have hMle : M ≤ Subgroup.centralizer ({B.t} : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h1 : ⁅m, B.t⁆ = 1 := by
      have hmem : ⁅m, B.t⁆ ∈ ⁅M, Subgroup.zpowers B.t⁆ :=
        Subgroup.commutator_mem_commutator hm (Subgroup.mem_zpowers B.t)
      rw [hMt] at hmem
      simpa using hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  exact hD.not_le (hMle.trans B.H_le_Hhat)

/-- **Bender Lemma 2.7(b)**: `[S,U] ⊄ F(U)`, with Bender 2.2 available. -/
theorem L27_su_not_le_h22_v12 : Work.CORE2B.L27_su_not_le_h22 :=
  L27su_of_gaps L27su_A_ne_bot_v12 L27_fourGroup_in_C_M_t L27su_transport

/-- **Bender Lemma 2.7 = the contract `Work.GW2.Lemma27Prop`**, complete: inputs are the toolkit,
Bender 2.2, Bender 2.3 and Theorem 2.6 (the amended list of the lead's design passes 6 and 12). -/
theorem lemma27 (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop)
    (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop) : Work.GW2.Lemma27Prop :=
  lemma27_of_leaves_h22 T h22 h23 h26 L27_commutator_le_v12 L27_su_not_le_h22_v12
    L27_solvable_v12

end Work.CORE2B
