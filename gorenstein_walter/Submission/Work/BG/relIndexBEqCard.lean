import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.Defs
import Submission.Work.BG.B_normalizes_K
import Submission.Work.BG.thmCSec3
import Submission.Work.BG.indexEqCardOfNormalSup

namespace Work.BG

/-- Let `D : Work.GW2.BGData G`, and let `K1`, `K2` be maximal odd-order subgroups of `H = C_G(t)` inverted by the involutions `t₁`, `t₂` respectively. Assume `B₁ = B₂` (so that `D.B = B₁ ⊓ B₂ = B₁ = U ⊓ C_G(t₁) = C_U(t₁)`) and `D.U = D.B ⊔ (K1 ⊓ K2)` (`U = O(H)`). Then the relative index of `B` in `U` is `|K₁ ⊓ K₂|`.

Route (all of it elementary):
* `K := K₁ ⊓ K₂ ≤ D.U` and `D.B ≤ D.U` directly from `hU`;
* `D.B ⊓ K = ⊥`: an element of `D.B ≤ C_G(t₁)` that also lies in `K ≤ K₁` is both centralized and inverted by `t₁`, so has order dividing `2` and odd order (see `Work.BG.thmCSec3_B_inf_K1` in `Submission/Work/BG/thmCSec3.lean`, which proves `D.B ⊓ K1 = ⊥`);
* `K ◁ D.U`: maximality of `K₁` gives `B` normalizes `K` (`Work.BG.B_normalizes_K`, i.e. `⁅D.B, K1 ⊓ K2⁆ ≤ K1 ⊓ K2`, in `Submission/Work/BG/B_normalizes_K.lean`), and trivially `K ≤ N_G(K)`, so `D.U = D.B ⊔ K ≤ N_G(K)`; then `Subgroup.normal_subgroupOf_iff_le_normalizer`;
* in `↥D.U` with `B' := D.B.subgroupOf D.U` and `K' := K.subgroupOf D.U` (where `K = K₁ ⊓ K₂`): `B' ⊔ K' = ⊤` and `B' ⊓ K' = ⊥` (from `Subgroup.subgroupOf_sup`, `Subgroup.comap_inf`), so `B'.index = Nat.card ↥K'` (e.g. via the general lemma `Work.BG.indexEqCardOfNormalSup`, or directly: `Subgroup.relIndex_sup_left` gives `K'.relIndex ⊤ = K'.relIndex B' = Nat.card ↥B'`, and Lagrange in `↥D.U`);
* conclude with `D.B.relIndex D.U = B'.index` (definitional) and `Nat.card ↥K' = Nat.card ↥K` (`Subgroup.subgroupOfEquivOfLe`). -/
theorem relIndexBEqCard {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (K1 K2 : Subgroup G)
    (hK1 : Work.GW2.IsMaxInverted D.H D.t1 K1) (hK2 : Work.GW2.IsMaxInverted D.H D.t2 K2)
    (hB : D.B1 = D.B2) (hU : D.U = D.B ⊔ (K1 ⊓ K2)) :
    D.B.relIndex D.U = Nat.card (K1 ⊓ K2 : Subgroup G) := by
  set K : Subgroup G := K1 ⊓ K2 with hK
  have hB_le_U : D.B ≤ D.U := by rw [hU]; exact le_sup_left
  have hK_le_U : K ≤ D.U := by rw [hU]; exact le_sup_right
  -- `D.B ⊓ K = ⊥`
  have hBinK : D.B ⊓ K = ⊥ := by
    rw [hK]
    refine le_bot_iff.mp ?_
    calc D.B ⊓ (K1 ⊓ K2) ≤ D.B ⊓ K1 := inf_le_inf_left D.B inf_le_left
      _ = ⊥ := thmCSec3_B_inf_K1 D K1 hK1
  -- `K ◁ D.U`
  have hnorm : D.U ≤ Subgroup.normalizer (K : Set G) := by
    rw [hU]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_normalizer_iff_commutator_le_right]
      simpa [hK] using B_normalizes_K D K1 K2 hK1 hK2
    · exact Subgroup.le_normalizer
  -- pass to the group `↥D.U`
  let K' : Subgroup ↥D.U := K.subgroupOf D.U
  have hK'normal : K'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_U).mpr hnorm
  have hsup : D.B.subgroupOf D.U ⊔ K' = ⊤ := by
    have h : (D.B ⊔ K).subgroupOf D.U = D.B.subgroupOf D.U ⊔ K' :=
      Subgroup.subgroupOf_sup hB_le_U hK_le_U
    rw [← h, show D.B ⊔ K = D.U from hU.symm]
    exact Subgroup.subgroupOf_self D.U
  have hinf : D.B.subgroupOf D.U ⊓ K' = ⊥ := by
    have h : (D.B ⊓ K).subgroupOf D.U = D.B.subgroupOf D.U ⊓ K' :=
      Subgroup.comap_inf D.B K (D.U).subtype
    rw [hBinK] at h
    rw [← h]
    exact Subgroup.bot_subgroupOf D.U
  have hidx : (D.B.subgroupOf D.U).index = Nat.card ↥K' :=
    indexEqCardOfNormalSup (D.B.subgroupOf D.U) K' hK'normal hsup hinf
  have hcard : Nat.card ↥K' = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_U).toEquiv
  show (D.B.subgroupOf D.U).index = Nat.card ↥K
  rw [hidx, hcard]

end Work.BG
