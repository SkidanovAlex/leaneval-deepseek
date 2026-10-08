import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.normalizer_eq_of_coatom
import Submission.Work.CORE3.NormalizerPcoreEqHhat

namespace Work.CORE3.FreeAux

theorem NormalizerU3 (G : Type) [Group G] [Finite G]
    (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3) :
    Subgroup.normalizer (B.U : Set G) = B.Hhat := by
  haveI : IsSimpleGroup G := hBc.simple
  -- Bender's Theorem 2.6 (`I.h26`): `U = O(H)` is exactly the odd core of `Ĥ`.
  have hU : Work.GW2.oddCoreIn B.Hhat = B.U := (I.h26 G I.T.ft hBc B).1
  have hUmap : (Work.GW2.oddCore ↥B.Hhat).map B.Hhat.subtype = B.U := by rw [← hU]; rfl
  -- `U ≤ Ĥ`, so `U ≠ ⊥` is forced by `|U| = 3`.
  have hUle : B.U ≤ B.Hhat := hUmap ▸ Subgroup.map_subtype_le _
  have hne : B.U ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (B.U : Subgroup G) = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  -- `U` is normal in `Ĥ`, so `Ĥ ≤ N_G(U)`.
  have hle : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    have h := Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
    rwa [hUmap] at h
  -- A nontrivial subgroup cannot be normal in the simple group `G` (as `U ≤ Ĥ ≠ ⊤`),
  -- so maximality of `Ĥ` forces `N_G(U) = Ĥ`.
  exact Work.CORE2A.normalizer_eq_of_coatom B.Hhat_coatom hUle hne hle

end Work.CORE3.FreeAux
