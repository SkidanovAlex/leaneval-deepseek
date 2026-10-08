/-
Copyright (c) 2024. All rights reserved.

# Layers of a Suzuki 2-group versus invariant subgroups of `P / Z(P)`

`ξ`-invariant layers `Z(P) ≤ M ≤ P` with `|M| = q ^ 2` correspond to `ξ`-invariant subgroups of
`Q = P / Z(P)` of order `q` (where `q = |Z(P)|`): the map is `M ↦ M / Z(P)`, and the inverse is
`N ↦ N.comap (P ⧸ Z(P))`.

This file proves the corresponding cardinality identity
`Work.Higman.card_layers_eq_card_quotient`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.typeB
import Submission.Work.Higman.Layers.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.Higman

/-- The automorphism of `P ⧸ Z(P)` induced by `ξ`. -/
def xiQuot {P : Type} [Group P] (ξ : MulAut P) : P ⧸ Subgroup.center P →* P ⧸ Subgroup.center P :=
  QuotientGroup.map _ _ (ξ : P →* P) fun z hz => by
    rw [← Subgroup.map_center_eq (ξ : P ≃* P)]
    exact Subgroup.mem_map_of_mem _ hz

theorem xiQuot_mk {P : Type} [Group P] (ξ : MulAut P) (a : P) :
    xiQuot ξ (QuotientGroup.mk' (Subgroup.center P) a) =
      QuotientGroup.mk' (Subgroup.center P) (ξ a) :=
  QuotientGroup.map_mk' _ _ _ _ a

variable {P : Type} [Group P] [Finite P]

/-- `|M / Z(P)| · |Z(P)| = |M|` for `Z(P) ≤ M`. -/
theorem card_map_quot_mul {M : Subgroup P} (hZ : Subgroup.center P ≤ M) :
    Nat.card ↥(M.map (QuotientGroup.mk' (Subgroup.center P))) * Nat.card ↥(Subgroup.center P) =
      Nat.card ↥M := by
  have hrange : ((QuotientGroup.mk' (Subgroup.center P)).comp M.subtype).range =
      M.map (QuotientGroup.mk' (Subgroup.center P)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : ((QuotientGroup.mk' (Subgroup.center P)).comp M.subtype).ker =
      (Subgroup.center P).subgroupOf M := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_subtype]
  have h1 : Nat.card ↥(((QuotientGroup.mk' (Subgroup.center P)).comp M.subtype).ker) *
      Nat.card ↥(((QuotientGroup.mk' (Subgroup.center P)).comp M.subtype).range) = Nat.card ↥M := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index _
  rw [hker, hrange] at h1
  rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv, mul_comm]

/-- `|N.comap (P ⧸ Z(P))| = |N| · |Z(P)|`. -/
theorem card_comap_quot (N : Subgroup (P ⧸ Subgroup.center P)) :
    Nat.card ↥(N.comap (QuotientGroup.mk' (Subgroup.center P))) =
      Nat.card ↥N * Nat.card ↥(Subgroup.center P) := by
  have hsurj : (QuotientGroup.mk' (Subgroup.center P)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  have hrange : ((QuotientGroup.mk' (Subgroup.center P)).comp
      (N.comap (QuotientGroup.mk' (Subgroup.center P))).subtype).range = N := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Subgroup.map_comap_eq_self (by rw [hsurj]; exact le_top)
  have hker : ((QuotientGroup.mk' (Subgroup.center P)).comp
      (N.comap (QuotientGroup.mk' (Subgroup.center P))).subtype).ker =
      (Subgroup.center P).subgroupOf (N.comap (QuotientGroup.mk' (Subgroup.center P))) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_subtype]
  have h1 : Nat.card ↥(((QuotientGroup.mk' (Subgroup.center P)).comp
        (N.comap (QuotientGroup.mk' (Subgroup.center P))).subtype).ker) *
      Nat.card ↥(((QuotientGroup.mk' (Subgroup.center P)).comp
        (N.comap (QuotientGroup.mk' (Subgroup.center P))).subtype).range) =
      Nat.card ↥(N.comap (QuotientGroup.mk' (Subgroup.center P))) := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index _
  rw [hker, hrange] at h1
  rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := Subgroup.center P)
    (K := N.comap (QuotientGroup.mk' (Subgroup.center P))) (fun z hz => by
      rw [Subgroup.mem_comap]
      have hz1 : QuotientGroup.mk' (Subgroup.center P) z = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff z).mpr hz
      rw [hz1]
      exact N.1.one_mem)).toEquiv, mul_comm]

/-- **Layers of `P` correspond to `ξ`-invariant subgroups of `P / Z(P)` of order `2 ^ n`.** -/
theorem card_layers_eq_card_quotient {ξ : MulAut P} {n : ℕ}
    (hZn : Nat.card ↥(Subgroup.center P) = 2 ^ n) :
    Nat.card {M : Subgroup P // IsXiLayer ξ M} =
      Nat.card {N : Subgroup (P ⧸ Subgroup.center P) //
        (∀ y ∈ N, xiQuot ξ y ∈ N) ∧ Nat.card ↥N = 2 ^ n} := by
  classical
  have hZs : Nat.card ↥(Subgroup.center P) = 2 ^ n := hZn
  have hZpos : 0 < Nat.card ↥(Subgroup.center P) := by rw [hZs]; positivity
  -- the underlying bijection
  have hmapsq : ∀ M : Subgroup P, (∀ x ∈ M, ξ x ∈ M) → M.map (ξ : P →* P) = M := by
    intro M hinv
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := hx
      exact hinv y hy
    · exact le_of_eq (Subgroup.card_map_of_injective (f := (ξ : P →* P))
        (K := M) (ξ : P ≃* P).injective).symm
  refine Nat.card_congr ?_
  refine
    { toFun := fun M => ⟨M.1.map (QuotientGroup.mk' (Subgroup.center P)), ?_, ?_⟩
      invFun := fun N => ⟨N.1.comap (QuotientGroup.mk' (Subgroup.center P)), ?_, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- invariance of the image
    intro y hy
    have h2 : (xiQuot ξ).comp (QuotientGroup.mk' (Subgroup.center P)) =
        (QuotientGroup.mk' (Subgroup.center P)).comp (ξ : P →* P) := by
      ext a
      exact xiQuot_mk ξ a
    have h3 : (M.1.map (QuotientGroup.mk' (Subgroup.center P))).map (xiQuot ξ) =
        M.1.map (QuotientGroup.mk' (Subgroup.center P)) := by
      rw [Subgroup.map_map, h2, ← Subgroup.map_map, hmapsq M.1 M.2.2.1]
    exact h3 ▸ Subgroup.mem_map_of_mem (xiQuot ξ) hy
  · -- cardinality of the image
    have h1 := card_map_quot_mul (P := P) M.2.1
    have hM : Nat.card ↥M.1 = 2 ^ (2 * n) := by
      rw [M.2.2.2, hZs, ← pow_mul]
      congr 1
      ring
    have h2 : Nat.card ↥(M.1.map (QuotientGroup.mk' (Subgroup.center P))) *
        Nat.card ↥(Subgroup.center P) = Nat.card ↥(Subgroup.center P) *
        Nat.card ↥(Subgroup.center P) := by
      rw [h1, hM, hZs, ← pow_add]
      congr 1
      ring
    have h3 : Nat.card ↥(M.1.map (QuotientGroup.mk' (Subgroup.center P))) =
        Nat.card ↥(Subgroup.center P) :=
      Nat.eq_of_mul_eq_mul_right (m := Nat.card ↥(Subgroup.center P)) hZpos h2
    rw [h3, hZs]
  · -- `Z ≤ comap`
    intro z hz
    rw [Subgroup.mem_comap]
    have hz1 : QuotientGroup.mk' (Subgroup.center P) z = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff z).mpr hz
    rw [hz1]
    exact N.1.one_mem
  · -- invariance of the comap
    intro x hx
    rw [Subgroup.mem_comap] at hx ⊢
    rw [← xiQuot_mk ξ x]
    exact N.2.1 _ hx
  · -- cardinality of the comap
    have h1 := card_comap_quot (P := P) N.1
    rw [h1, N.2.2, hZs]
    ring
  · -- left inverse
    intro M
    refine Subtype.ext ?_
    exact Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (Subgroup.center P))
      (by rw [QuotientGroup.ker_mk']; exact M.2.1)
  · -- right inverse
    intro N
    refine Subtype.ext ?_
    exact Subgroup.map_comap_eq_self (f := QuotientGroup.mk' (Subgroup.center P)) (by
      rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      exact le_top)

end Work.Higman

namespace Work.Higman

open Layers

end Work.Higman
