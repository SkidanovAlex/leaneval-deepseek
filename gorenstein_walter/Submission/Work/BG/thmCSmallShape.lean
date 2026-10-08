import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.Defs
import Submission.Work.BG.hyp12OfBGData
import Submission.Work.BG.splitglue.Split
import Submission.Work.BG.thmCSmallAux
import Submission.Work.BG.b1InfK2EqBot
import Submission.Work.BG.kEqTwoMulCard

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem thmCSmallShape : Work.GW2.C16.ThmCSmallShapeProp := by
  intro G _ _ D K1 K2 hn hK1 hK2 hdir
  -- (A) consequences of `|S₀| = 2`: `t = t₁t₂`, `t₁t₂ = t₂t₁`, `B₁ = B₂`, `S ≤ C(tᵢ)`.
  obtain ⟨_ht12, _hcomm, hB, hSleC1, hSleC2⟩ := thmCSmallAux D hn
  -- (B) `H = O(H) · S` (Bender's splitting, ported to the `Work.GW2` vocabulary).
  have hcentr : ∀ x ∈ (D.S : Subgroup G), x * D.t = D.t * x := fun x hx =>
    ((Subgroup.mem_centralizer_iff.mp (BGData_S_le_centralizer_t D hx)) D.t
      (Set.mem_singleton D.t)).symm
  have hUS : D.U ⊔ (D.S : Subgroup G) = D.H :=
    SplitGlue.centralizerSplitProp G D.S D.n D.two_le D.dih D.t (D.S0_le D.t_mem) D.t_order hcentr
  -- (C) `B₁ ∩ K₂ = 1`, so the direct decomposition collapses to `U = B · K`.
  have hA : D.B1 ⊓ K2 = ⊥ := b1InfK2EqBot D K2 hn hK2
  have hU : D.U = D.B ⊔ (K1 ⊓ K2) := by
    have h := hdir.1
    rw [hA, bot_sup_eq] at h
    exact h.symm
  -- (D) `k = 2 |K₁ ∩ K₂|`.
  have hk : D.k = 2 * Nat.card (K1 ⊓ K2 : Subgroup G) :=
    kEqTwoMulCard D K1 K2 hn hK1 hK2 hUS hSleC1 hSleC2 hB hU
  exact ⟨hU, hk⟩

end Work.BG
