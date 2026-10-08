import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.BSW.Cases.K4.CardSup

/-!
# `|Ĥ : H| = 3` in subcase (1b) of Bender 1981, §3

Bender 1981, Theorem 2.6 (`Work.GW2.Thm26Prop`) says that either `O₂(Ĥ) ≤ S₀` and `Ĥ = H`, or
`V := O₂(Ĥ)` is a four-group with `(V ⊔ U).relIndex Ĥ = 6` (that is, `Ĥ/O₂(Ĥ)U ≅ D₃`).

In §3 subcase (1b) one is in the second alternative, and then

* `V ≤ S ⊓ C_G(U) ≤ S ≤ H`, `U ≤ H` and `H = U ⊔ S` (Bender p. 219,
  `Work.CORE3.H_eq_U_sup_S`);
* `U = O(H) ⊴ H`, so `S` and `V` both normalize `U`; together with `U ⊓ S = 1`
  (`Work.CORE2A.inf_U_S_eq_bot`) and `U ⊓ V ≤ U ⊓ S = 1` this gives
  `|H| = |U| · |S| = 8|U|` and `|V ⊔ U| = |V| · |U| = 4|U|`;
* hence `|H : VU| = 2`, and `|Ĥ : H| · 2 = |Ĥ : VU| = 6` gives `|Ĥ : H| = 3`.

The main mathematical input is the first alternative of Theorem 2.6 being ruled out: it puts the
four-group `V` inside the cyclic group `S₀`, and a four-group is not cyclic.
-/

namespace Work.CORE3

open Work.GW2

/-- A subgroup of a cyclic group is cyclic. -/
theorem isCyclic_of_le_of_isCyclic' {G : Type} [Group G] {A C : Subgroup G} (hAC : A ≤ C)
    (hC : IsCyclic C) : IsCyclic A := by
  haveI : IsCyclic ↥(A.subgroupOf C) := inferInstance
  exact (Subgroup.subgroupOfEquivOfLe hAC).isCyclic.mp inferInstance

/-- A Klein four-group is not cyclic: a cyclic group of order `4` has an element of order `4`,
whereas every element of a four-group has order at most `2`. -/
theorem not_isCyclic_of_isFourGroup' {G : Type} [Group G] {V : Subgroup G}
    (h : IsFourGroup V) : ¬ IsCyclic V := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := V)
  have hgm : orderOf (g : G) = Nat.card V := by
    simpa using (Subgroup.orderOf_mk (g : G) g.2).symm.trans hg
  have hle : orderOf (g : G) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr (h.2 (g : G) g.2))
  rw [hgm, h.1] at hle
  omega

/-- The image in `G` of a normal subgroup of `↥K` is normalized by `K`. -/
theorem le_normalizer_map_subtype_of_normal' {G : Type} [Group G] {K : Subgroup G}
    {N : Subgroup K} (hN : N.Normal) :
    K ≤ Subgroup.normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk n hn
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
  exact Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * m * ⟨k, hk⟩⁻¹, hN.conj_mem m hm ⟨k, hk⟩, by simp⟩

/-- Bender 1981 §3, subcase (1b): if `Case1 B` holds and `O₂(Ĥ)` is a four-group, then
`O₂(Ĥ)U` has index `2` in `H = C_G(t)`. -/
theorem relIndex_pCoreIn_sup_U_H {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) :
    (pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.H = 2 := by
  classical
  have hfourV : IsFourGroup (pCoreIn 2 B.Hhat) := D.four
  -- `V ≤ S ≤ H`, `U ≤ H`, and `U = O(H) ⊴ H`.
  have hV_le_S : pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := by
    rw [← (I.h26 G I.T.ft hBc B).2.1]
    exact inf_le_left
  have hU_le_H : B.U ≤ B.H := Work.CORE2A.bSetup_U_le_H B
  have hS_le_H : (B.S : Subgroup G) ≤ B.H := Work.CORE2A.bSetup_S_le_H B
  have hV_le_H : pCoreIn 2 B.Hhat ≤ B.H := le_trans hV_le_S hS_le_H
  have hH_le_NU : B.H ≤ Subgroup.normalizer (B.U : Set G) :=
    le_normalizer_map_subtype_of_normal' (K := B.H) (N := Work.GW2.oddCore ↥B.H) inferInstance
  have hS_le_NU : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
    le_trans hS_le_H hH_le_NU
  have hV_le_NU : pCoreIn 2 B.Hhat ≤ Subgroup.normalizer (B.U : Set G) :=
    le_trans hV_le_H hH_le_NU
  have hUV : B.U ⊓ pCoreIn 2 B.Hhat = ⊥ := by
    have h : B.U ⊓ pCoreIn 2 B.Hhat ≤ B.U ⊓ (B.S : Subgroup G) :=
      inf_le_inf le_rfl hV_le_S
    rw [Work.CORE2A.inf_U_S_eq_bot B] at h
    exact le_bot_iff.mp h
  -- Cardinalities.
  have hcardH : Nat.card ↥B.H = Nat.card ↥B.U * 8 := by
    rw [← H_eq_U_sup_S G I.T hBc B,
      Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hS_le_NU
        (Work.CORE2A.inf_U_S_eq_bot B), D.S8]
  have hcardW : Nat.card ↥(pCoreIn 2 B.Hhat ⊔ B.U) = Nat.card ↥B.U * 4 := by
    rw [sup_comm, Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hV_le_NU hUV,
      hfourV.1]
  -- `|H : VU| = 2`.
  have hmul := Subgroup.relIndex_mul_card (H := pCoreIn 2 B.Hhat ⊔ B.U) (K := B.H)
  rw [inf_eq_left.mpr (sup_le hV_le_H hU_le_H), hcardW, hcardH] at hmul
  have hpos : 0 < Nat.card ↥B.U * 4 := Nat.mul_pos Nat.card_pos (by norm_num)
  have hkey : (pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.H * (Nat.card ↥B.U * 4)
      = 2 * (Nat.card ↥B.U * 4) := by
    rw [hmul]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos hkey

theorem RelIndexHHhat {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) :
    B.H.relIndex B.Hhat = 3 := by
  have hfourV : IsFourGroup (pCoreIn 2 B.Hhat) := D.four
  -- Bender's Theorem 2.6: the first alternative is impossible, so `Ĥ/O₂(Ĥ)U ≅ D₃`.
  have hrel6 : (pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 := by
    rcases (I.h26 G I.T.ft hBc B).2.2 with ⟨hle, -⟩ | ⟨-, h6, -⟩
    · exact absurd (isCyclic_of_le_of_isCyclic' hle B.S0_cyclic)
        (not_isCyclic_of_isFourGroup' hfourV)
    · exact h6
  -- `O₂(Ĥ)U ≤ H ≤ Ĥ`
  have hV_le_S : pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := by
    rw [← (I.h26 G I.T.ft hBc B).2.1]
    exact inf_le_left
  have hW_le_H : pCoreIn 2 B.Hhat ⊔ B.U ≤ B.H :=
    sup_le (le_trans hV_le_S (Work.CORE2A.bSetup_S_le_H B)) (Work.CORE2A.bSetup_U_le_H B)
  -- `|H : VU| · |Ĥ : H| = |Ĥ : VU| = 6` with `|H : VU| = 2`.
  have hmul := Subgroup.relIndex_mul_relIndex (H := pCoreIn 2 B.Hhat ⊔ B.U) (K := B.H)
    (L := B.Hhat) hW_le_H B.H_le_Hhat
  rw [relIndex_pCoreIn_sup_U_H I hBc B h1 D, hrel6] at hmul
  omega

end Work.CORE3
