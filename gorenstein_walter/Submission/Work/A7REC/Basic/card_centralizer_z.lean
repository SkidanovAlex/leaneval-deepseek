/-
Area `A7REC` (recognition of `A₇`), file `Basic/card_centralizer_z.lean`.

# `|C_G(z)| = 24`

Let `G` be a finite group satisfying the `A₇` hypotheses (`A7RecCtx G`): `z` is the central
involution of a Sylow `2`-subgroup `S` isomorphic to the dihedral group of order `8`, and
`C_G(z) = U ⊔ S` with `|U| = 3` and `U` normal in `C_G(z)`.

Since `|U| = 3` and `|S| = 8` are coprime, `U ⊓ S = ⊥`; since `S` normalizes `U` (it lies in
`C_G(z) = U ⊔ S` and `U ⊴ C_G(z)`), the join `U ⊔ S = C_G(z)` has exactly `|U| · |S| = 24`
elements, the general fact that a join of two subgroups with one normalizing the other and
trivial intersection is an internal direct product.

Everything reduces to `|C_G(z)| = |U| · |S| = 3 · 8 = 24`.  The converse is what makes this
consistent with `A₇`: for the central involution `z = (1 2)(3 4)` of `A₇`, `C_{A₇}(z)` has
order `24`.
-/
import Mathlib
import Submission.Work.A7REC.Defs

namespace Work.A7REC.Basic

open Subgroup

/-- **Cardinality of a join with a normalizing factor.**  If `B` normalizes `A` and `A ⊓ B = ⊥`,
then `A ⊔ B` is the internal direct product of `A` and `B`: `|A ⊔ B| = |A| · |B|`.

(Normality of `A` in `A ⊔ B` makes `↑(A ⊔ B) = ↑A * ↑B`, so that the multiplication map
`A × B → A ⊔ B` is onto; it is injective because `A ⊓ B = ⊥`.  This is the same statement as
`OddOrder.BG.Ch1.S03f.card_sup_of_le_normalizer_of_disjoint` of the `OddOrder` area, reproduced
here so that this file is self-contained; a general-purpose copy is proved in
`Submission/Work/A7REC/Join/card_sup_of_le_normalizer_of_disjoint.lean`.) -/
theorem card_sup_mul_card_of_le_normalizer_of_disjoint {G : Type*} [Group G] {A B : Subgroup G}
    (hn : B ≤ Subgroup.normalizer (A : Set G)) (hd : Disjoint A B) :
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

variable {G : Type*} [Group G] [Finite G]

/-- A Sylow `2`-subgroup of a group satisfying the `A₇` hypotheses has `8` elements, because it
is isomorphic to `DihedralGroup 4` and `|DihedralGroup n| = 2n`. -/
theorem card_Ssub_eq_eight (ctx : Work.A7REC.A7RecCtx G) : Nat.card (ctx.S : Subgroup G) = 8 := by
  obtain ⟨e⟩ := ctx.hSdih
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

/-- **`|C_G(z)| = 24`.**  `C_G(z) = U ⊔ S` with `|U| = 3`, `|S| = 8`, `U ⊆ N_G(S)`-side
condition `U ⊴ C_G(z)` and `gcd 3 8 = 1`; hence `C_G(z)` is the direct product `U × S` of the
two subgroups and has order `3 · 8 = 24`. -/
theorem card_centralizer_z (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    Nat.card (Subgroup.centralizer ({ctx.z} : Set G)) = 24 := by
  have hS8 : Nat.card (ctx.S : Subgroup G) = 8 := card_Ssub_eq_eight ctx
  -- `U ⊴ C_G(z)` and `S ≤ C_G(z)` give `S ≤ N_G(U)`.
  have hn : (ctx.S : Subgroup G) ≤ Subgroup.normalizer (ctx.U : Set G) :=
    le_trans ctx.S_le_C ((Subgroup.normal_subgroupOf_iff_le_normalizer ctx.U_le_C).mp ctx.hUnorm)
  -- `|U| = 3` and `|S| = 8` are coprime, so `U ⊓ S = ⊥`.
  have hd : Disjoint ctx.U (ctx.S : Subgroup G) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [ctx.hUcard, hS8]
    decide
  rw [ctx.hCz, card_sup_mul_card_of_le_normalizer_of_disjoint hn hd, ctx.hUcard, hS8]

end Work.A7REC.Basic
