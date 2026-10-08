/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.dihedral_index_two

/-!
# Lower bound for the number of involutions in a dihedral Sylow 2-subgroup

This is one of the leaves of the area `CORE2A`.  Let `S` be a Sylow `2`-subgroup of a finite
group `G` whose `2`-subgroup is dihedral, `S ≅ DihedralGroup n` with `n ≥ 2`.  If `S₀ ≤ S` is a
*cyclic* subgroup of index `2` in `S` and `t ∈ S₀` has order `2`, then `S` contains at least
`|S₀| + 1` involutions.

Mathematically: `|S| = 2n` and `|S₀| = n`.  Every element of `S \ S₀` is an involution (this is
`Work.CORE2A.dihedral_index_two`), as is `t ∈ S₀`, and the two families are disjoint.  Hence the
number of involutions in `S` is at least `|S \ S₀| + 1 = (2n - n) + 1 = n + 1 = |S₀| + 1`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

theorem involutions_dihedral_lower {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (n : ℕ)
    (hn : 2 ≤ n) (hiso : Nonempty ((S : Subgroup G) ≃* DihedralGroup n)) (S0 : Subgroup G)
    (hS0 : S0 ≤ S) (hcyc : IsCyclic S0) (hidx : S0.relIndex (S : Subgroup G) = 2)
    (t : G) (ht : t ∈ S0) (ht2 : orderOf t = 2) :
    Nat.card S0 + 1 ≤ (Set.ncard {x : G | x ∈ (S : Subgroup G) ∧ orderOf x = 2}) := by
  classical
  -- Every element of `S` outside the cyclic subgroup `S₀` is an involution.
  have hdihedral : ∀ s ∈ (S : Subgroup G), s ∉ S0 → orderOf s = 2 :=
    dihedral_index_two n hn (S : Subgroup G) S0 hiso hS0 hcyc hidx
  -- Cardinality facts: `|S| = 2n` and `|S₀| = n`.
  obtain ⟨e⟩ := hiso
  have hcardS : Nat.card (S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcardS0 : Nat.card S0 = n := by
    have h := Subgroup.relIndex_mul_card S0 (S : Subgroup G)
    rw [hidx, inf_eq_left.mpr hS0, hcardS] at h
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) h
  -- The set of involutions of `S` and the "other coset" `D = S \ S₀`.
  set Inv : Set G := {x : G | x ∈ (S : Subgroup G) ∧ orderOf x = 2} with hInv
  set D : Set G := (S : Set G) \ (S0 : Set G) with hDdef
  have hsub : (S0 : Set G) ⊆ (S : Set G) := fun x hx => hS0 hx
  have hSsncard : (S : Set G).ncard = 2 * n := by
    rw [← Nat.card_coe_set_eq (S : Set G)]
    exact hcardS
  have hS0ncard : (S0 : Set G).ncard = n := by
    rw [← Nat.card_coe_set_eq (S0 : Set G)]
    exact hcardS0
  -- `|D| = |S| - |S₀| = 2n - n = n`.
  have hDncard : D.ncard = n := by
    rw [hDdef, Set.ncard_sdiff hsub, hSsncard, hS0ncard]
    omega
  -- Every element of `D` is an involution.
  have hDsub : D ⊆ Inv := by
    intro x hx
    rw [hDdef] at hx
    obtain ⟨hxS, hx0⟩ := hx
    exact ⟨hxS, hdihedral x hxS hx0⟩
  -- `t` is an involution of `S₀`, hence of `Inv`, and lies outside `D`.
  have htInv : t ∈ Inv := ⟨hS0 ht, ht2⟩
  have htnot : t ∉ D := by
    rw [hDdef]
    intro h
    exact h.2 ht
  -- Therefore `Inv` contains the disjoint union `D ∪ {t}`, of size `n + 1`.
  have hIns : insert t D ⊆ Inv := by
    intro x hx
    rcases hx with rfl | hx
    · exact htInv
    · exact hDsub hx
  have hle : (insert t D).ncard ≤ Inv.ncard := Set.ncard_le_ncard hIns
  rw [Set.ncard_insert_of_notMem htnot, hDncard] at hle
  rw [hcardS0]
  exact hle

end Work.CORE2A
