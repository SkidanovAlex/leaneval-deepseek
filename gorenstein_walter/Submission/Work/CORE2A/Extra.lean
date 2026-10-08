/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic

/-!
# CORE2A: further API (commuting joins, maximal inverted subgroups, `F*`)

Small but useful consequences of the vocabulary, proved once and for all:

* a join of two commutative subgroups that centralize each other is commutative
  (`isMulCommutative_sup_of_le_centralizer`) — this is what makes `K = U × S₀` abelian in
  Bender's Lemma 2.2;
* the largest odd subgroup inverted by `s` is unique (`IsMaxInverted.unique`) — used when
  applying BG Theorem C;
* one involution class gives conjugacy (`OneInvClassIn.isConj`);
* `F*(X) = F(X) E(X)` and `F*(X) = F(X)` when `E(X) = 1`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

variable {G : Type*}

/-! ## 1. Joins of commuting commutative subgroups -/

theorem mul_comm_of_mem_of_isMulCommutative {G : Type*} [Group G] {H : Subgroup G}
    (hH : IsMulCommutative H) {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : H) ⟨y, hy⟩)

theorem isMulCommutative_sup_of_le_centralizer {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : K ≤ Subgroup.centralizer (H : Set G)) (hH : IsMulCommutative H)
    (hK : IsMulCommutative K) : IsMulCommutative (H ⊔ K : Subgroup G) := by
  have hsup : H ⊔ K ≤ Subgroup.centralizer (((H ⊔ K : Subgroup G)) : Set G) := by
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
    refine (Subgroup.closure_le (K := Subgroup.centralizer ((H : Set G) ∪ (K : Set G)))).mpr ?_
    intro x hx
    change x ∈ Subgroup.centralizer ((H : Set G) ∪ (K : Set G))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hx with hxH | hxK
    · rcases hy with hyH | hyK
      · exact mul_comm_of_mem_of_isMulCommutative hH hyH hxH
      · exact ((Subgroup.mem_centralizer_iff.mp (hHK hyK)) x hxH).symm
    · rcases hy with hyH | hyK
      · exact (Subgroup.mem_centralizer_iff.mp (hHK hxK)) y hyH
      · exact mul_comm_of_mem_of_isMulCommutative hK hyK hxK
  refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
  have hx : (x : G) ∈ Subgroup.centralizer (((H ⊔ K : Subgroup G)) : Set G) := hsup x.2
  exact ((Subgroup.mem_centralizer_iff.mp hx) (y : G) y.2).symm

/-! ## 2. Maximal inverted subgroups -/

theorem IsMaxInverted.unique {G : Type*} [Group G] {H : Subgroup G} {s : G} {K K' : Subgroup G}
    (h : IsMaxInverted H s K) (h' : IsMaxInverted H s K') : K = K' :=
  le_antisymm (h'.2.2.2 K h.1 h.2.1 h.2.2.1) (h.2.2.2 K' h'.1 h'.2.1 h'.2.2.1)

/-! ## 3. One involution class -/

theorem OneInvClassIn.isConj {G : Type*} [Group G] {K : Subgroup G} (h : OneInvClassIn K)
    {x y : G} (hx : x ∈ K) (hy : y ∈ K) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) :
    ∃ g ∈ K, g * x * g⁻¹ = y :=
  h x ⟨hx, hx2⟩ y ⟨hy, hy2⟩

/-! ## 4. `F*(X)` -/

theorem fstarIn_eq_sup (G : Type*) [Group G] (K : Subgroup G) :
    fstarIn K = fittingIn K ⊔ layerIn K :=
  Subgroup.map_sup _ _ _

theorem fstarIn_eq_fittingIn_of_layerIn_eq_bot {G : Type*} [Group G] {K : Subgroup G}
    (h : layerIn K = ⊥) : fstarIn K = fittingIn K := by
  rw [fstarIn_eq_sup, h, sup_bot_eq]

/-! ## 5. `BenderSetup` complements -/

theorem bSetup_S0_le_H {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    B.S0 ≤ B.H := le_trans B.S0_le (bSetup_S_le_H B)

theorem bSetup_S0_le_Hhat {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    B.S0 ≤ B.Hhat := le_trans (bSetup_S0_le_H B) B.H_le_Hhat

theorem bSetup_t_mem_S0 {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    B.t ∈ B.S0 := B.t_mem

theorem bSetup_card_S0_dvd {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    Nat.card B.S0 ∣ Nat.card (B.S : Subgroup G) :=
  ⟨2, by rw [Nat.mul_comm (Nat.card B.S0) 2]; exact bSetup_card_S_eq B⟩

theorem bSetup_H_le_S_le_iff {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    {x : G} (hx : x ∈ B.H) : x ∈ B.Hhat := B.H_le_Hhat hx

/-! ## 6. `Inverts` and centralizers, complements -/

theorem inverts_conjSub_eq {G : Type*} [Group G] {s : G} {K : Subgroup G} (h : Inverts s K) :
    conjSub s K = K := by
  refine le_antisymm (inverts_conjSub_le h) ?_
  have h' : conjSub s (conjSub s⁻¹ K) ≤ conjSub s K :=
    conjSub_mono (inverts_conjSub_le (inverts_symm h)) s
  rwa [conjSub_conjSub_inv] at h'

theorem mem_centralizer_singleton {G : Type*} [Group G] {x y : G} :
    x ∈ Subgroup.centralizer ({y} : Set G) ↔ y * x = x * y := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h; exact h y (by simp)
  · intro h z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact h

end Work.CORE2A
