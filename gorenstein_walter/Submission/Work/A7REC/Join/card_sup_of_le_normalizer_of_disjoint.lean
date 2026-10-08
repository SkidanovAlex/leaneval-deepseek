/-
Area `A7REC`: a general group-theoretic tool.

If `B` normalizes `A` and `A ⊓ B = ⊥`, then `A ⊔ B` is the internal direct product of `A` and
`B`, so `|A ⊔ B| = |A| · |B|`.  (In the area this is used with `A = U`, `B = S` to get
`|C_G(z)| = |U ⊔ S| = 24`, and with `A = U`, `B = U^g` to get a subgroup of order `9`.)

The same statement appears as `Work.A7REC.Basic.card_sup_mul_card_of_le_normalizer_of_disjoint`
inside `Basic/card_centralizer_z.lean`; this module is the standalone, dependency-free copy.
-/
import Mathlib

namespace Work.A7REC.Join

open Subgroup

theorem card_sup_of_le_normalizer_of_disjoint {G : Type*} [Group G]
    {A B : Subgroup G} (hn : B ≤ Subgroup.normalizer (A : Set G)) (hd : Disjoint A B) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  set S : Subgroup G := A ⊔ B with hS
  have hA_le : A ≤ S := le_sup_left
  have hB_le : B ≤ S := le_sup_right
  have hnorm : S ≤ Subgroup.normalizer (A : Set G) := sup_le le_normalizer hn
  have hAnormal : ((A.subgroupOf S) : Subgroup ↥S).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  -- `A.subgroupOf S` and `B.subgroupOf S` are complementary in `↥S`.
  have hcompl : Subgroup.IsComplement' (A.subgroupOf S) (B.subgroupOf S) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
      rw [Subgroup.mem_inf] at hx
      simp only [Subgroup.mem_subgroupOf] at hx
      have hmem : (x : G) ∈ A ⊓ B := ⟨hx.1, hx.2⟩
      rw [hd.eq_bot, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact Subtype.ext (by simpa using hmem)
    · have hsup : ((A.subgroupOf S) : Subgroup ↥S) ⊔ (B.subgroupOf S) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hA_le hB_le, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul ((A.subgroupOf S) : Subgroup ↥S) (B.subgroupOf S)
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hcard := hcompl.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le).toEquiv] at hcard
  exact hcard.symm

end Work.A7REC.Join
