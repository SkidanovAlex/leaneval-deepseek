import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.ChV12.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|D| = |Inv(Q)|` for split rank-one data with `Q` a `2`-group

Let `H` be strongly embedded in the finite group `G`, `t ∉ H` an involution with `H` acting
Zassenhaus (trivially) on `G ⧸ H`, and `Q ≤ H` a non-trivial normal subgroup with
`H = Q ⋊ D`, where `D = H ∩ H^t` (the two-point stabiliser, of odd order).  Then

  `|D| = |Inv(Q)|`,

the number of involutions of the root group `Q` equals the order of the two-point stabiliser.

This is the counting identity behind the classification of the Zassenhaus groups with abelian
and with Suzuki root groups: in `PSL(2, 2ⁿ)` the group `Q` is elementary abelian of order `q`
and `D` is cyclic of order `q - 1`, while in `Sz(2^{2n+1})` the group `Q` is a Suzuki 2-group
of order `q²` whose involutions form `Z(Q) = Ω₁(Q)` of order `q`, again with `|D| = q - 1`.

The proof has three ingredients, none of which uses `Q ≠ ⊥` or `IsPGroup 2 Q` (those are only
carried along because the request mentions them):

* `Kset_eq_twoPoint_of_invert` : `K = J(D,t) = {x ∈ D | x^t = x⁻¹}` **is** all of `D`.  Here
  Zassenhausness enters through `t_conj_eq_inv`: `t` inverts every element of `D`.
* `Work.ThmF.Bender.cardKsetEqInv` (Peterfalvi I, Ch. I §2 Prop. 1 (c), from the delivered
  chapter-I library): `|K| = |Inv(H)|`.  Hence `|D| = |Inv(H)|`.
* `involutions_H_eq_involutions_Q` : `Inv(H) = Inv(Q)`.  Indeed `|H| = |Q|·|D|` is the order of
  the semidirect product `H = Q ⋊ D` with `|D|` odd, so `H/Q ≅ D` has odd order, and an element
  of order `2` of `H` therefore maps to `1` in `H/Q`.

The same identity is derived independently in the sibling file `ZData.feit_bound`
(`ncard_involutions_Q_eq_card_twoPoint`) from Peterfalvi's transitivity of `D` on `Inv(H)` and
the fixed-point-freeness of `D` on `Q#`; the present proof instead isolates the counting
theorem `|K| = |Inv(H)|` of Chapter I §2.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2.ZData

variable {G : Type} [Group G] [Finite G]

/-! ## `Q` has odd index in `H` and contains all involutions of `H` -/

/-- `Q` and `Q.subgroupOf H` have the same order when `Q ≤ H`. -/
private theorem card_subgroupOf_eq_card {H Q : Subgroup G} (hle : Q ≤ H) :
    Nat.card ↥(Q.subgroupOf H) = Nat.card Q :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

/-- An involution of a group lies in every normal subgroup of odd index: otherwise its image in
the odd-order quotient would have order `two`. -/
private theorem mem_of_orderOf_eq_two_of_odd_index_quot {N : Subgroup G} [N.Normal]
    (hodd : Odd N.index) {x : G} (hx : orderOf x = 2) : x ∈ N := by
  by_contra hxN
  have hdvd : orderOf (QuotientGroup.mk' N x) ∣ 2 := by
    rw [← hx]; exact orderOf_map_dvd (QuotientGroup.mk' N) x
  have hne1 : orderOf (QuotientGroup.mk' N x) ≠ 1 := by
    intro h1
    refine hxN ?_
    have hker : x ∈ (QuotientGroup.mk' N).ker := by
      rw [MonoidHom.mem_ker]; exact orderOf_eq_one_iff.mp h1
    rwa [QuotientGroup.ker_mk'] at hker
  have htwo : orderOf (QuotientGroup.mk' N x) = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left hne1
  have hdvd2 : 2 ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact htwo ▸ orderOf_dvd_natCard (QuotientGroup.mk' N x)
  exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdvd2)

/-- In split rank-one data `H = Q ⋊ D` with `D = H ∩ H^t` of odd order, every involution of
`H` lies in the regular normal subgroup `Q` (Peterfalvi I, Ch. I §2: `Inv(H) ⊆ Q`). -/
private theorem involution_mem_Q_of_odd_index {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {u : G} (hu : u ∈ involutions (H : Set G)) : u ∈ Q := by
  obtain ⟨huH, hu2⟩ := hu
  haveI : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  have hidx : (Q.subgroupOf H).index = Nat.card (twoPoint H t) := by
    have hmul : (Q.subgroupOf H).index * Nat.card ↥(Q.subgroupOf H) = Nat.card H :=
      Subgroup.index_mul_card _
    rw [card_subgroupOf_eq_card h.le,
      Work.ThmF.card_H_eq_mul_of_data (Work.ThmF.IsSplitRankOne.toData h)] at hmul
    rw [mul_comm (Nat.card Q) (Nat.card (twoPoint H t))] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hodd : Odd (Q.subgroupOf H).index := by
    rw [hidx]
    exact h.stronglyEmbedded.2.2 t h.not_mem
  have hu2H : orderOf (⟨u, huH⟩ : ↥H) = 2 := by
    rw [Subgroup.orderOf_mk u huH]; exact hu2
  exact Subgroup.mem_subgroupOf.mp (mem_of_orderOf_eq_two_of_odd_index_quot (G := ↥H) hodd hu2H)

/-- The involutions of `H` are exactly the involutions of `Q`. -/
private theorem involutions_H_eq_involutions_Q {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) :
    involutions (H : Set G) = involutions (Q : Set G) := by
  ext u
  constructor
  · intro hu
    exact ⟨involution_mem_Q_of_odd_index h hu, hu.2⟩
  · intro hu
    exact ⟨h.le hu.1, hu.2⟩

/-! ## `K = J(D,t)` is all of `D` -/

/-- In a split rank-one group with Zassenhaus action the Weyl element `t` inverts the
two-point stabiliser, so `K = J(D,t) = {x ∈ D | x^t = x⁻¹}` is all of `D = twoPoint H t`. -/
private theorem Kset_eq_twoPoint_of_invert {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (hQ : Q ≠ ⊥) (h2 : IsPGroup 2 Q) :
    Work.ThmF.Kset H t = (twoPoint H t : Set G) := by
  ext x
  rw [Work.ThmF.mem_Kset_iff]
  constructor
  · exact fun hx => hx.1
  · intro hx
    exact ⟨hx, by
      rw [Work.ZassenhausPSL2.t_inv h]
      exact t_conj_eq_inv H Q t h hz hQ h2 x hx⟩

/-! ## The count -/

theorem card_dStab_eq_card_involutions {G : Type} [Group G] [Finite G] (H Q : Subgroup G) (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (hQ : Q ≠ ⊥) (h2 : IsPGroup 2 Q) :
    Nat.card (Submission.Blueprint.twoPoint H t)
      = (Submission.Blueprint.involutions (Q : Set G)).ncard := by
  have hK : Work.ThmF.Kset H t = (Submission.Blueprint.twoPoint H t : Set G) :=
    Kset_eq_twoPoint_of_invert h hz hQ h2
  have hI : Submission.Blueprint.involutions (H : Set G)
      = Submission.Blueprint.involutions (Q : Set G) :=
    involutions_H_eq_involutions_Q h
  calc Nat.card (Submission.Blueprint.twoPoint H t)
      = ((Submission.Blueprint.twoPoint H t : Subgroup G) : Set G).ncard :=
        Nat.card_coe_set_eq _
    _ = (Work.ThmF.Kset H t).ncard := by rw [hK]
    _ = (Submission.Blueprint.involutions (H : Set G)).ncard :=
        Work.ThmF.Bender.cardKsetEqInv h.stronglyEmbedded h.invol h.not_mem
    _ = (Submission.Blueprint.involutions (Q : Set G)).ncard := by rw [hI]

end Work.ZassenhausPSL2.ZData
