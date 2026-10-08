/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.OddOrder.Isaacs.Ch01_Sylow.Basic

/-!
# CORE2A: bridges and elementary consequences for the assembly `thm26_of_steps`

Nothing here is specific to Theorem 2.6: this module only

* identifies the contract's `Work.GW2.fitting` / `Work.GW2.pCore` with the odd-order
  library's `OddOrder.Isaacs.Ch01.fitting` / `…opCore` (the same statements are proved in
  `Submission.Work.GLUE.Bridge`, which however cannot be imported together with
  `Submission.Work.CORE2A.Defs` because `GLUE.Defs` re-declares the whole `Work.GW2`
  vocabulary);
* converts the "relative" versions `…In K` back to subgroups of `↥K`;
* relates the cardinality of a proper subgroup to that of the ambient finite group.

They are collected in a separate module so that the delegated leaves of
`Work.CORE2A.thm26_of_steps` can import them (the main file of the assembly imports the
leaves, so a leaf cannot import it).
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

/-- `F(G)` in the contract's sense is Isaacs' Fitting subgroup. -/
theorem fitting_eq_isaacsFitting {G : Type} [Group G] [Finite G] :
    Work.GW2.fitting G = OddOrder.Isaacs.Ch01.fitting G := by
  have hS : sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N}
      = OddOrder.Isaacs.Ch01.fitting G := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hnil⟩
      haveI : N.Normal := hN
      haveI : Group.IsNilpotent ↥N := hnil
      exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    · exact ⟨OddOrder.Isaacs.Ch01.fitting.normal G,
        OddOrder.Isaacs.Ch01.fitting.isNilpotent⟩
  rw [Work.GW2.fitting, hS]
  exact Subgroup.normalCore_eq_self _

/-- `O_p(G)` in the contract's sense is Isaacs' `p`-core. -/
theorem pCore_eq_opCore {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.GW2.pCore p G = OddOrder.Isaacs.Ch01.opCore p G := by
  have hS : sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}
      = OddOrder.Isaacs.Ch01.opCore p G := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hpN⟩
      exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore (N := N) hpN
    · exact ⟨OddOrder.Isaacs.Ch01.opCore.normal p G,
        OddOrder.Isaacs.Ch01.opCore_isPGroup p G⟩
  rw [Work.GW2.pCore, hS]
  exact Subgroup.normalCore_eq_self _

/-- `Work.GW2.layerIn K = ⊥` says that `K` has no normal quasisimple subgroup. -/
theorem layer_eq_bot_of_layerIn_eq_bot {G : Type*} [Group G] {K : Subgroup G}
    (h : Work.GW2.layerIn K = ⊥) : Work.GW2.layer K = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective (Work.GW2.layer K) K.subtype_injective).mp h

/-- `O_p(K) = 1` for a subgroup, read off from the relative version. -/
theorem pCore_eq_bot_of_pCoreIn_eq_bot {G : Type*} [Group G] {p : ℕ} {K : Subgroup G}
    (h : Work.GW2.pCoreIn p K = ⊥) : Work.GW2.pCore p K = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective (Work.GW2.pCore p K) K.subtype_injective).mp h

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
theorem card_lt_card_of_ne_top {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (h : K ≠ ⊤) : Nat.card ↥K < Nat.card G := by
  haveI : Finite (G ⧸ K) := Quotient.finite _
  have hidx : 1 < K.index := Subgroup.one_lt_index_of_ne_top h
  have hpos : 0 < Nat.card ↥K := Nat.card_pos
  have hlt : Nat.card ↥K < K.index * Nat.card ↥K := by
    calc Nat.card ↥K = 1 * Nat.card ↥K := (one_mul _).symm
      _ < K.index * Nat.card ↥K := Nat.mul_lt_mul_of_pos_right hidx hpos
  have := Subgroup.index_mul_card (H := K)
  omega

end Work.CORE2A
