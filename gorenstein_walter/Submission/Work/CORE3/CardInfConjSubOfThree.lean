import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.J4.CardDvdSixOfDisjoint
import Submission.Work.CORE3.J4.J4DTriv
import Submission.Work.CORE3.CosetInvCountNeFive
import Submission.Work.CORE3.J4.J4CosetStep
import Submission.Work.CORE3.BenderSevenU3

/-!
# CORE3: Bender (7), second half (`|Ĥ ⊓ Ĥ^y| = 6`), extracted from `BenderSevenD6`

`Work.CORE3.card_inf_conjSubOfThree` is Bender 1981 §3, step (7), second half, in the form used
by `Work.CORE3.Case1bStabTrivial`: from `|U| = 3` and `cosetInvCount Ĥ y = 4` one gets
`|Ĥ ⊓ Ĥ^y| = 6`.

It is kept in this low module — rather than in `Submission/Work/CORE3/BenderSevenD6.lean`, where
it was first written — because `BenderSevenD6` imports `Case1bSeven`, whose closure now contains
`Case1bStabTrivial` (through `J4/J4Seven*`, `VUCardTwelve` and `Case1bDiv`).  The present module
imports only proof-free material, so `Case1bStabTrivial` can cite it.
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- **Assembly.**  Bender 1981, §3, step (7), second half: given `|U| = 3` and that the coset
`Ĥy` carries exactly four involutions, the intersection `Ĥ ⊓ Ĥ^y` has order `6`.

`Dsub := Ĥ ⊓ Ĥ^y` and `W := O₂(Ĥ) ⊔ O(Ĥ)`: `|Ĥ : W| = 6`.  From `4 ≤ cosetInvCount Ĥ y`
(Bender's (6)/(7)) we get `Dsub · W = Ĥ` (`Case1bDStructure`), while `Dsub ⊓ W = ⊥` is
`J4.J4DTriv`.  Hence `|Dsub| * |W| = |Dsub ⊔ W| = |Ĥ| = 6 * |W|`, so `|Dsub| = 6`. -/
theorem card_inf_conjSubOfThree
    {G : Type} [Group G] [Finite G] (I : Case1Inputs) (hBc : BenderCtx G) (B : BenderSetup G)
    (h1 : Case1 B) (D : Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (X : Subgroup G) (hXle : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : Inverts y X)
    (hCeven : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hNeven : Even (Nat.card (Subgroup.normalizer (X : Set G))))
    (hU3 : Nat.card B.U = 3)
    (hy4 : cosetInvCount B.Hhat y = 4) :
    Nat.card ↥(B.Hhat ⊓ conjSub y B.Hhat) = 6 := by
  classical
  set W : Subgroup G := pCoreIn 2 B.Hhat ⊔ B.U with hW
  set Dsub : Subgroup G := B.Hhat ⊓ conjSub y B.Hhat with hDsub
  have hWrel : W.relIndex B.Hhat = 6 := by
    rw [hW]; exact relIndex_VU_Hhat G I hBc B h1 D
  have hWn : (W.subgroupOf B.Hhat).Normal := by
    rw [hW]; exact normal_VU_subgroupOf G I hBc B h1 D
  -- `W ≤ Ĥ`
  have h26 : Thm26Concl B := I.h26 G I.T.ft hBc B
  have hWle : W ≤ B.Hhat := by
    rw [hW]
    exact sup_le (Work.CORE2A.thm26Concl_O2_le_Hhat h26) (Work.CORE2A.thm26Concl_U_le_Hhat h26)
  -- `Dsub ≤ Ĥ`
  have hDle : Dsub ≤ B.Hhat := by rw [hDsub]; exact inf_le_left
  -- `Ĥ ≤ N(W)`
  have hnormW : B.Hhat ≤ Subgroup.normalizer (W : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact (Subgroup.normal_subgroupOf_iff hWle).mp hWn a k ha hk
    · intro ha
      have h2 : k⁻¹ * (k * a * k⁻¹) * (k⁻¹)⁻¹ ∈ W :=
        (Subgroup.normal_subgroupOf_iff hWle).mp hWn (k * a * k⁻¹) k⁻¹ ha (B.Hhat.inv_mem hk)
      have h3 : k⁻¹ * (k * a * k⁻¹) * (k⁻¹)⁻¹ = a := by group
      rwa [h3] at h2
  -- Bender's (6)/(7) from `4 ≤ cosetInvCount Ĥ y`
  have h4 : 4 ≤ cosetInvCount B.Hhat y := by omega
  obtain ⟨hsup, -, -⟩ := Case1bDStructure G I hBc B h1 D y hy2 hyH h4
  -- the J₄ stabilizer result
  have htriv : W ⊓ Dsub = ⊥ := by
    rw [hW, hDsub]
    exact Work.CORE3.J4.J4DTriv (X := X) I hBc B h1 D hy2 hyH hy4 hXle hXne hXodd hinv
      hCeven hNeven hU3
  -- cardinality: `|W| * |Dsub| = |Ĥ| = 6 * |W|`
  have hcard := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot
    (H := W) (K := Dsub) (le_trans hDle hnormW) (by simpa [inf_comm] using htriv)
  have hDsup : W ⊔ Dsub = B.Hhat := by rw [sup_comm]; exact hsup
  rw [hDsup] at hcard
  have hHhat : Nat.card ↥B.Hhat = 6 * Nat.card ↥W := by
    have h := Subgroup.relIndex_mul_card (H := W) (K := B.Hhat)
    rw [inf_eq_left.mpr hWle, hWrel] at h
    exact h.symm
  rw [hHhat] at hcard
  have h6 : Nat.card ↥W * 6 = Nat.card ↥W * Nat.card ↥Dsub := by
    rw [mul_comm (Nat.card ↥W) 6]
    exact hcard
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h6).symm


end Work.CORE3
