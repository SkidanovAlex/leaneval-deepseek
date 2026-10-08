import Mathlib
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.lemma4
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThreePoints.involutions_commute_of_below

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12` — foundational facts for Ch. V §2 Lemma 6

Throughout, `G` is a finite group in a situation `(B0)–(B2)`, `H = Q ⋊ D` is a split rank-one
datum (`IsSplitRankOne H Q t`), `s ∈ Q` an involution with `orderOf (s * t) = 3` (`Hyp5`).
This file collects the translations used by `lemma6`:

* `Z(Q) = Q0sub H` (Higman: the centre of a Suzuki 2-group is `Ω₁`);
* `W = C_V(K)` centralises `Q0sub H`;
* `W ⊆ D = twoPoint H t` has odd order.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs
open scoped commutatorElement

namespace Work.ThmF.ChV12

open Submission.Blueprint Work.ThmF

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-! ## §1. Involutions of `H` lie in `Q` -/

/-- Every involution of `H` lies in `Q` (since `H/Q ≅ D` has odd order). -/
theorem inv_mem_Q (h : IsSplitRankOne H Q t) :
    ∀ u ∈ involutions (H : Set G), u ∈ Q := by
  intro u hu
  haveI : (Q.subgroupOf H).Normal := split_Q_normal_in_H h
  have hQHindex : (Q.subgroupOf H).index = Nat.card ↥(twoPoint H t) := by
    have hcard := Subgroup.card_mul_index (Q.subgroupOf H)
    have h1 : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
    rw [h1, split_card_H h] at hcard
    exact Nat.mul_left_cancel Nat.card_pos hcard
  have hu2 : orderOf (⟨u, hu.1⟩ : ↥H) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hu.2
  have hmem : (⟨u, hu.1⟩ : ↥H) ∈ Q.subgroupOf H :=
    Work.ThreePoints.mem_of_orderOf_eq_two_of_odd_index
      (L := Q.subgroupOf H) (by rw [hQHindex]; exact split_odd_card_twoPoint h) hu2
  exact Subgroup.mem_subgroupOf.mp hmem

/-- The involutions of `H` and of `Q` coincide. -/
theorem involutions_H_eq_Q (h : IsSplitRankOne H Q t) :
    involutions (H : Set G) = involutions (Q : Set G) := by
  ext u
  exact ⟨fun hu => ⟨inv_mem_Q h u hu, hu.2⟩, fun hu => ⟨h.le hu.1, hu.2⟩⟩

/-- `Q0sub H ≤ Q`. -/
theorem Q0sub_le_Q (h : IsSplitRankOne H Q t) : Q0sub H ≤ Q := by
  rw [Q0sub]
  refine (Subgroup.closure_le Q).mpr ?_
  intro x hx
  rcases mem_Q0_iff.mp hx with ⟨hxH, hx2⟩ | rfl
  · exact inv_mem_Q h x ⟨hxH, hx2⟩
  · exact Q.one_mem

/-! ## §2. `Z(Q) = Q0sub H` -/

/-- **`Z(Q) = Q0sub H`.**  By Higman (applied to the Suzuki 2-group `Q`) the centre of `Q` is the
set `{z | z² = 1}`, i.e. `Ω₁(Q)`; and `Ω₁(Q) = ⟨Inv(Q)⟩ = ⟨Inv(H)⟩ = Q0sub H`. -/
theorem center_eq_subgroupOf (hC4 : ChIIFourProp) (h : Lemma5.Hyp5 H Q t s)
    (hHig : HigmanProp) (hSuz : IsSuzukiTwoGroup ↥Q) :
    Subgroup.center ↥Q = (Q0sub H).subgroupOf Q := by
  have hcomm := involutions_of_H_commute h.sit hC4 H Q t h.split
  have hQ0 := Q0sub_elementary H hcomm
  have hZ := (hHig ↥Q hSuz).1
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hx2 : x ^ 2 = 1 := (hZ x).mp hx
    have hx2' : (x : G) ^ 2 = 1 := by
      have := congrArg (fun z : ↥Q => (z : G)) hx2
      simpa using this
    rcases eq_or_ne (x : G) 1 with h1 | h1
    · rw [h1]; exact (Q0sub H).one_mem
    · have ho : orderOf (x : G) = 2 := orderOf_eq_prime hx2' h1
      exact Q0_le_Q0sub H (mem_Q0_iff.mpr (Or.inl ⟨h.split.le x.2, ho⟩))
  · intro hx
    rw [hZ]
    have h1 : (x : G) * (x : G) = 1 := hQ0.1 (x : G) hx
    apply Subtype.ext
    simpa [pow_two] using h1

/-- `|Z(Q)| = |Q0sub H|`. -/
theorem card_center_eq (hC4 : ChIIFourProp) (h : Lemma5.Hyp5 H Q t s)
    (hHig : HigmanProp) (hSuz : IsSuzukiTwoGroup ↥Q) :
    Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Q0sub H) := by
  rw [center_eq_subgroupOf hC4 h hHig hSuz]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q0sub_le_Q h.split)).toEquiv

/-- `Q` has class `2`: every commutator is central. -/
theorem commutator_mem_center (hHig : HigmanProp) (hSuz : IsSuzukiTwoGroup ↥Q) :
    ∀ x y : ↥Q, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center ↥Q := by
  intro x y
  have hc := (hHig ↥Q hSuz).2.2.1
  have h1 : ⁅x, y⁆ ∈ commutator ↥Q :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  rw [hc] at h1
  show x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center ↥Q
  simpa [commutatorElement_def] using h1

/-- Squares of elements of the Suzuki 2-group `Q` are central. -/
theorem sq_mem_center (hHig : HigmanProp) (hSuz : IsSuzukiTwoGroup ↥Q) :
    ∀ x : ↥Q, x ^ 2 ∈ Subgroup.center ↥Q :=
  (hHig ↥Q hSuz).2.1

/-- Central elements of `Q` are involutions. -/
theorem center_sq_eq_one (hHig : HigmanProp) (hSuz : IsSuzukiTwoGroup ↥Q) :
    ∀ z : ↥Q, z ∈ Subgroup.center ↥Q → z ^ 2 = 1 :=
  fun z hz => ((hHig ↥Q hSuz).1 z).mp hz

/-! ## §3. `W` centralises `Q0sub H` -/

/-- `W = C_V(K)` as an intersection: `W = D ⊓ C_G(Inv H)` (Peterfalvi II Ch. II §4 Prop. 4). -/
theorem W_eq_twoPoint_inter_cent_inv (hC4 : ChIIFourProp) (hS : Situation G)
    (h : IsSplitRankOne H Q t) :
    W H t = twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)) := by
  have hP4 := (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).2.2.2.2.1
  show centD H t ⊓ Subgroup.centralizer (Kset H t) = _
  rw [show Kset H t = invertedBy (twoPoint H t) t from rfl]
  exact hP4

/-- `W ≤ C_G(Q0sub H)`. -/
theorem W_le_centralizer_Q0sub (hC4 : ChIIFourProp) (hS : Situation G)
    (h : IsSplitRankOne H Q t) :
    W H t ≤ Subgroup.centralizer (Q0sub H : Set G) := by
  rw [W_eq_twoPoint_inter_cent_inv hC4 hS h]
  intro w hw
  have hwc : ∀ x ∈ involutions (H : Set G), x * w = w * x :=
    fun x hx => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 x hx
  have hle : Q0sub H ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [Q0sub]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases mem_Q0_iff.mp hx with ⟨hxH, hx2⟩ | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hwc x ⟨hxH, hx2⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one])
  exact Subgroup.mem_centralizer_iff.mpr
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hle hx))

/-- `W ≤ D = twoPoint H t`. -/
theorem W_le_twoPoint (H : Subgroup G) (t : G) : W H t ≤ twoPoint H t :=
  le_trans (W_le_centD H t) (centD_le_twoPoint (H := H) t)

/-- `|W|` is odd (as `W ≤ D`, of odd order). -/
theorem odd_card_W (h : IsSplitRankOne H Q t) : Odd (Nat.card ↥(W H t)) := by
  have hodd : Odd (Nat.card ↥(twoPoint H t)) := split_odd_card_twoPoint h
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le (W_le_twoPoint H t))

end Work.ThmF.ChV12
