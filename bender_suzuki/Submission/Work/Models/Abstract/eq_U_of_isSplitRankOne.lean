import Mathlib
import Submission.Work.Models.Abstract.twoPoint_eq
import Submission.Work.Models.Abstract.involutions_subset_U
import Submission.Work.Models.Port.BenderSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.Abstract.eq_U_of_isSplitRankOne`

A `BenderPair P` packages the abstract rank-one `(B,N)`-pair of characteristic two attached to a
strongly embedded subgroup: `B` strongly embedded, `U ◁ B` a Sylow `2`-subgroup, `T` an odd order
complement of `U` in `B`, and `[G : B] = |U| + 1`.

The two-point stabiliser of a point outside the base point is `D = B ⊓ Bᵗ` for
`t ∉ B`, which by `Work.Models.Abstract.twoPoint_eq` is a `B`-conjugate of `T`; hence
`|D| = |T|` is *odd*.  Any split rank-one datum `(B, Q, t)` has `Q ◁ B` (with `Q ≤ B`) and
`B = Q ⊔ D`, `Q ⊓ D = ⊥`, so `|B| = |Q| · |D| = |Q| · |T|`, while `|B| = |U| · |T|`; cancelling
`|T|` gives `|Q| = |U|`.  Moreover `[B : Q] = |D| = |T|` is odd, so the image of the `2`-group `U`
in `B ⧸ Q` lies in a group of odd order and is again a `2`-group: it is trivial, i.e.
`U ≤ Q`.  With `|U| = |Q|` this forces `Q = U`.

The uniqueness of `Q` is what makes the phrase "the unipotent radical" legitimate for a split
rank-one datum: the datum is determined by `B` and the involution `t`.

The general group-theoretic ingredient is isolated in `le_of_coprime_card_index`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint (involutions twoPoint IsSplitRankOne)
open Commons.GroupTheory.Subgroup (card_sup_of_inf_eq_bot_of_le_normalizer)

namespace Work.Models.Abstract

/-- **A normal subgroup whose index is prime to `|U|` contains `U`.**  If `Q ◁ B` (`Q ≤ B` with
`B ≤ N_G(Q)`) and `U ≤ B` has order coprime to the index `[B : Q]`, then `U ≤ Q`.

Indeed the order of the image of `u ∈ U` in the quotient `B ⧸ Q` divides both `|U|` and
`[B : Q] = |B ⧸ Q|`, hence is `1`. -/
theorem le_of_coprime_card_index {G : Type*} [Group G] [Finite G] {B Q U : Subgroup G}
    (hQB : Q ≤ B) (hN : B ≤ Subgroup.normalizer (Q : Set G)) (hUB : U ≤ B)
    (hcop : Nat.Coprime (Nat.card ↥U) (Q.subgroupOf B).index) : U ≤ Q := by
  haveI : (Q.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQB).mpr hN
  intro u hu
  -- The image of `u` in `B ⧸ Q`.
  let φ : ↥U →* (↥B ⧸ Q.subgroupOf B) :=
    (QuotientGroup.mk' (Q.subgroupOf B)).comp (Subgroup.inclusion hUB)
  have h1 : orderOf (φ ⟨u, hu⟩) ∣ Nat.card ↥U :=
    (orderOf_map_dvd φ (⟨u, hu⟩ : ↥U)).trans (orderOf_dvd_natCard (⟨u, hu⟩ : ↥U))
  have h2 : orderOf (φ ⟨u, hu⟩) ∣ (Q.subgroupOf B).index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard (φ ⟨u, hu⟩)
  have hone : orderOf (φ ⟨u, hu⟩) = 1 :=
    (Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2
  have hker : (Subgroup.inclusion hUB ⟨u, hu⟩ : ↥B) ∈
      (QuotientGroup.mk' (Q.subgroupOf B)).ker := by
    rw [MonoidHom.mem_ker]
    exact orderOf_eq_one_iff.mp hone
  have hmem : (Subgroup.inclusion hUB ⟨u, hu⟩ : ↥B) ∈ Q.subgroupOf B := by
    rwa [QuotientGroup.ker_mk'] at hker
  exact Subgroup.mem_subgroupOf.mp hmem

theorem eq_U_of_isSplitRankOne {G : Type} [Group G] [Finite G] (P : Submission.BenderPair G)
    {Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne P.B Q t) : Q = P.U := by
  classical
  -- ## Step 1.  `D = B ⊓ Bᵗ` is a `B`-conjugate of the torus, so `|D| = |T|`.
  have htB : t ∉ P.B := h.not_mem
  obtain ⟨b, _hb, c, _hc, _hbc, hDc⟩ := Work.Models.Abstract.twoPoint_eq P htB
  have hcardD : Nat.card ↥(twoPoint P.B t) = Nat.card ↥P.T := by
    rw [hDc]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  -- ## Step 2.  `B = Q ⊔ D` with `Q ⊓ D = ⊥` and `D ≤ N_G(Q)` gives `|B| = |Q| · |D|`.
  have hDnorm : twoPoint P.B t ≤ Subgroup.normalizer (Q : Set G) :=
    le_trans inf_le_left h.normal
  have hcardBQ : Nat.card ↥P.B = Nat.card ↥Q * Nat.card ↥(twoPoint P.B t) := by
    conv_lhs => rw [← h.sup_eq]
    exact card_sup_of_inf_eq_bot_of_le_normalizer Q _ hDnorm h.inf_eq
  -- ## Step 3.  Comparing with `|B| = |U| · |T|` gives `|Q| = |U|`.
  have hcardQ : Nat.card ↥Q = Nat.card ↥P.U := by
    have hpos : 0 < Nat.card ↥P.T := by
      haveI : Nonempty ↥P.T := ⟨1⟩
      exact Nat.card_pos
    refine Nat.mul_right_cancel hpos ?_
    rw [← hcardD, ← hcardBQ, Submission.BenderPair.card_eq_card_U_mul_card_T, hcardD]
  -- ## Step 4.  `[B : Q] = |T|` is odd, so the 2-group `U ≤ B` lies in `Q`.
  have hidxQ : (Q.subgroupOf P.B).index = Nat.card ↥P.T := by
    have hcardQg : Nat.card ↥(Q.subgroupOf P.B) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
    have hpos : 0 < Nat.card ↥Q := by
      haveI : Nonempty ↥Q := ⟨1⟩
      exact Nat.card_pos
    refine Nat.mul_right_cancel hpos ?_
    calc (Q.subgroupOf P.B).index * Nat.card ↥Q
        = (Q.subgroupOf P.B).index * Nat.card ↥(Q.subgroupOf P.B) := by rw [hcardQg]
      _ = Nat.card ↥P.B := Subgroup.index_mul_card _
      _ = Nat.card ↥Q * Nat.card ↥(twoPoint P.B t) := hcardBQ
      _ = Nat.card ↥P.T * Nat.card ↥Q := by rw [hcardD, Nat.mul_comm]
  have hoddQ : Odd (Q.subgroupOf P.B).index := by
    rw [hidxQ]
    exact P.hoddT
  obtain ⟨k, hk⟩ := P.hU2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥P.U) (Q.subgroupOf P.B).index := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.coprime_two_right.mpr hoddQ).symm)
  have hUleQ : P.U ≤ Q := le_of_coprime_card_index h.le h.normal P.U_le_B hcop
  -- ## Step 5.  `U ≤ Q` and `|Q| = |U|` force `Q = P.U`.
  exact (Subgroup.eq_of_le_of_card_ge hUleQ (le_of_eq hcardQ)).symm

end Work.Models.Abstract
