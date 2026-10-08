import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.Defs
import Submission.Work.BG.kEqSmall
import Submission.Work.BG.relIndexInfEqOfSupTop
import Submission.Work.BG.indexEqCardOfNormalSup
import Submission.Work.BG.uSubgroupOfNormalSupTop
import Submission.Work.BG.relIndexBEqCard

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem kEqTwoMulCard {G : Type} [Group G] [Finite G] (D : BGData G) (K1 K2 : Subgroup G)
    (hn : D.n = 2) (hK1 : IsMaxInverted D.H D.t1 K1) (hK2 : IsMaxInverted D.H D.t2 K2)
    (hUS : D.U ⊔ (D.S : Subgroup G) = D.H)
    (hSleC1 : (D.S : Subgroup G) ≤ Subgroup.centralizer ({D.t1} : Set G))
    (hSleC2 : (D.S : Subgroup G) ≤ Subgroup.centralizer ({D.t2} : Set G))
    (hB : D.B1 = D.B2) (hU : D.U = D.B ⊔ (K1 ⊓ K2)) :
    D.k = 2 * Nat.card (K1 ⊓ K2 : Subgroup G) := by
  -- `B = B₁ = U ⊓ C_G(t₁)` because `B₁ = B₂`.
  have hB_eq : D.B = D.B1 := by
    show D.B1 ⊓ D.B2 = D.B1
    rw [hB, inf_idem]
  -- `U ≤ H` since `U ⊔ S = H`.
  have hUH : D.U ≤ D.H := by rw [← hUS]; exact le_sup_left
  -- `k₁ = k₂`: for `|S| = 4` one has `C_H(t₁) = C_H(t₂)` (`Work.BG.kEqSmall`).
  have h12 : (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H =
      (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H := Work.BG.kEqSmall G D hn
  -- `B.relIndex U = |K₁ ⊓ K₂|`.
  have h3 : D.B.relIndex D.U = Nat.card (K1 ⊓ K2 : Subgroup G) :=
    relIndexBEqCard D K1 K2 hK1 hK2 hB hU
  -- `k₁ = |K₁ ⊓ K₂|`: the second isomorphism theorem in `↥H`, where `U ◁ H = U ⊔ C_H(t₁)`.
  have h2 : (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H =
      Nat.card (K1 ⊓ K2 : Subgroup G) := by
    obtain ⟨hPn, hPY⟩ := uSubgroupOfNormalSupTop D hUS hSleC1
    have hstep := relIndexInfEqOfSupTop (D.U.subgroupOf D.H)
      ((Subgroup.centralizer ({D.t1} : Set G)).subgroupOf D.H) hPn hPY
    show ((Subgroup.centralizer ({D.t1} : Set G)).subgroupOf D.H).index =
      Nat.card (K1 ⊓ K2 : Subgroup G)
    rw [hstep]
    have hCU : Subgroup.centralizer ({D.t1} : Set G) ⊓ D.U = D.B := by
      rw [inf_comm]
      show D.U ⊓ Subgroup.centralizer ({D.t1} : Set G) = D.B1 ⊓ D.B2
      rw [← hB, inf_idem]
    have hinf : (Subgroup.centralizer ({D.t1} : Set G)).subgroupOf D.H ⊓ D.U.subgroupOf D.H =
        D.B.subgroupOf D.H := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        ← hCU, Subgroup.mem_inf]
    rw [hinf, Subgroup.relIndex_subgroupOf hUH, h3]
  have hk2 : (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H =
      Nat.card (K1 ⊓ K2 : Subgroup G) := by
    rw [← h12]; exact h2
  calc D.k = (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H +
        (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H := rfl
    _ = 2 * Nat.card (K1 ⊓ K2 : Subgroup G) := by rw [h2, hk2]; ring

end Work.BG
