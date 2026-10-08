import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.CORE3.RelIndexHHhat

/-!
# `|Ĥ| = 72` in Bender 1981 §3, subcase (1b), from `|U| = 3`

Bender 1981, Theorem 2.6 says that in subcase `Ĥ ≠ H` the four-group `V = O₂(Ĥ)` satisfies
`Ĥ/V·U ≅ D₃`.  Together with `H = U ⊔ S` (`Work.CORE3.H_eq_U_sup_S`), `U ⊓ S = 1`
(`Work.CORE2A.inf_U_S_eq_bot`) and `|S| = 8` (`Case1bData.S8`) this gives

* `|Ĥ : H| = 3` (`Work.CORE3.RelIndexHHhat`),
* `|H| = |U| · |S| = 8·3 = 24`,

hence `|Ĥ| = 3 · 24 = 72`.  This file records the conclusion under a stable name.
-/

namespace Work.CORE3.FreeAux

open Work.GW2

/-- In Bender's §3 subcase (1b), `|U| = 3` forces `|Ĥ| = 72`. -/
theorem CardHhat72 (G : Type) [Group G] [Finite G]
    (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3) :
    Nat.card B.Hhat = 72 := by
  -- `|Ĥ : H| = 3` (Theorem 2.6: `Ĥ/VU ≅ D₃`, and `|H : VU| = 2`).
  have hrel : B.H.relIndex B.Hhat = 3 := Work.CORE3.RelIndexHHhat I hBc B h1 D
  have hcardHhat : Nat.card B.Hhat = 3 * Nat.card ↥B.H := by
    have h := Subgroup.relIndex_mul_card (H := B.H) (K := B.Hhat)
    rw [inf_eq_left.mpr B.H_le_Hhat, hrel] at h
    exact h.symm
  -- `S` normalizes `U = O(H)` (indeed `H ≤ N(U)`), so `|H| = |U ⊔ S| = |U| · |S|`.
  have hSNU : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
    le_trans (Work.CORE2A.bSetup_S_le_H B)
      (Work.CORE3.le_normalizer_map_subtype_of_normal' (K := B.H) (N := Work.GW2.oddCore ↥B.H)
        inferInstance)
  have hcardH : Nat.card ↥B.H = 24 := by
    rw [← Work.CORE3.Work.CORE3.H_eq_U_sup_S G I.T hBc B,
      Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hSNU
        (Work.CORE2A.inf_U_S_eq_bot B), hU3, D.S8]
  rw [hcardHhat, hcardH]

end Work.CORE3.FreeAux
