import Mathlib
import Submission.Work.PSU3.BenderST
import Submission.Work.PSU3.BenderST.transport
import Submission.Work.PSU3.BST.psu3_wTrans
import Submission.Work.Models.Abstract.exists_conj_eq
import Submission.Work.Models.Abstract.twoPoint_eq
import Submission.Work.Models.Abstract.involutions_subset_U
import Submission.Work.Models.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.BenderST.reduction` — every split rank-one datum is conjugate to the standard one

Given a `BenderPair P` (a "standard datum" `(P.B, P.U, P.w)`), every split rank-one datum
`(B,U,w)` of the group is conjugate to it: `∃ g, conj g B = P.B ∧ conj g U = P.U ∧
MulAut.conj g w = P.w`.  This is what reduces `BenderSTProp` to a computation in the three
models.

* `datum_conj_eq_general`: the case `B = P.B`.  `U` is identified with `P.U` by cardinality
  and Sylow uniqueness (`Work.PSU3.BenderST.datum_conj_eq` contains the same argument), and
  `w` is conjugated to `P.w` by the general transitivity lemma
  `Work.PSU3.BST.transitive_involutions_outside'` (which does *not* assume that `w` inverts
  the torus — that hypothesis fails for `PSU(3,2ⁿ)`).
* `datum_conj_standard`: the general case, using `Work.Models.Abstract.exists_conj_eq` and
  `isSplitRankOne_map`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint (involutions twoPoint IsAbelianSubgroup IsSplitRankOne)

namespace Work.PSU3.BenderST

/-- Every split rank-one datum whose point stabiliser is `P.B` is `P.B`-conjugate to the
standard datum `(P.B, P.U, P.w)`. -/
theorem datum_conj_eq_general {G : Type} [Group G] [Finite G] (P : Submission.BenderPair G)
    (hstd : IsSplitRankOne P.B P.U P.w)
    {Q : Subgroup G} {t : G} (h : IsSplitRankOne P.B Q t) :
    ∃ g ∈ P.B, Submission.Blueprint.conj g Q = P.U ∧ MulAut.conj g t = P.w := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## Step 1.  `t ∉ B` exhibits `D` as a conjugate of the torus, so `|D| = |T|`.
  have htB : t ∉ P.B := h.not_mem
  obtain ⟨b, hb, c, hc, hbc, hDc⟩ := Work.Models.Abstract.twoPoint_eq P htB
  have hcardD : Nat.card ↥(twoPoint P.B t) = Nat.card ↥P.T := by
    rw [hDc]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  -- ## Step 2.  `B = Q ⊔ D` with `Q ⊓ D = ⊥` and `D ≤ N(Q)` gives `|B| = |Q| · |D|`.
  have hDnorm : twoPoint P.B t ≤ Subgroup.normalizer (Q : Set G) :=
    le_trans inf_le_left h.normal
  have hcardBQ : Nat.card ↥P.B = Nat.card ↥Q * Nat.card ↥(twoPoint P.B t) := by
    conv_lhs => rw [← h.sup_eq]
    exact Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer Q _
      hDnorm h.inf_eq
  -- ## Step 3.  Comparing with `|B| = |U| · |T|` gives `|Q| = |U|`.
  have hcardQ : Nat.card ↥Q = Nat.card ↥P.U := by
    have hpos : 0 < Nat.card ↥P.T := by
      haveI : Nonempty ↥P.T := ⟨1⟩
      exact Nat.card_pos
    refine Nat.mul_right_cancel hpos ?_
    rw [← hcardD, ← hcardBQ, P.card_eq_card_U_mul_card_T, hcardD]
  -- ## Step 4.  `U ≤ Q`: the quotient `B ⧸ Q` has odd order `|T|`, while `U` is a 2-group.
  have hQnorm : (Q.subgroupOf P.B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
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
  have hoddQ : Odd (Nat.card (↥P.B ⧸ Q.subgroupOf P.B)) := by
    rw [← Subgroup.index_eq_card, hidxQ]
    exact P.hoddT
  obtain ⟨k, hk⟩ := P.hU2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥P.U) (Nat.card (↥P.B ⧸ Q.subgroupOf P.B)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.coprime_two_right.mpr hoddQ).symm)
  haveI := hQnorm
  have hUleQ : P.U ≤ Q := by
    intro u hu
    let φ : ↥P.U →* (↥P.B ⧸ Q.subgroupOf P.B) :=
      (QuotientGroup.mk' (Q.subgroupOf P.B)).comp (Subgroup.inclusion P.U_le_B)
    have h1 : orderOf (φ ⟨u, hu⟩) ∣ Nat.card ↥P.U :=
      (orderOf_map_dvd φ (⟨u, hu⟩ : ↥P.U)).trans
        (orderOf_dvd_natCard (⟨u, hu⟩ : ↥P.U))
    have h2 : orderOf (φ ⟨u, hu⟩) ∣ Nat.card (↥P.B ⧸ Q.subgroupOf P.B) :=
      orderOf_dvd_natCard (φ ⟨u, hu⟩)
    have hone : orderOf (φ ⟨u, hu⟩) = 1 :=
      (Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2
    have hmem : (Subgroup.inclusion P.U_le_B ⟨u, hu⟩ : ↥P.B) ∈ Q.subgroupOf P.B := by
      have hker : (Subgroup.inclusion P.U_le_B ⟨u, hu⟩ : ↥P.B) ∈
          (QuotientGroup.mk' (Q.subgroupOf P.B)).ker := by
        rw [MonoidHom.mem_ker]
        exact orderOf_eq_one_iff.mp hone
      rwa [QuotientGroup.ker_mk'] at hker
    exact Subgroup.mem_subgroupOf.mp hmem
  -- ## Step 5.  `U ≤ Q` and `|Q| = |U|` force `Q = P.U`.
  have hQU : Q = P.U :=
    (Subgroup.eq_of_le_of_card_ge hUleQ (le_of_eq hcardQ)).symm
  -- ## Step 6.  The general transitivity lemma conjugates `t` to `P.w`.
  obtain ⟨a, ha, haeq⟩ :=
    Work.PSU3.BST.transitive_involutions_outside' (H := P.B) (Q := P.U) (t := P.w) hstd
      h.invol h.not_mem
  refine ⟨a⁻¹, P.B.inv_mem ha, ?_, ?_⟩
  · rw [hQU]
    exact Work.Models.conj_self_of_mem_normalizer (H := P.U) (hstd.normal (P.B.inv_mem ha))
  · rw [MulAut.conj_apply, haeq]
    group

/-- **Every split rank-one datum is conjugate to the standard datum of the Bender pair.** -/
theorem datum_conj_standard {G : Type} [Group G] [Finite G] (P : Submission.BenderPair G)
    (hstd : IsSplitRankOne P.B P.U P.w)
    {B U : Subgroup G} {w : G} (h : IsSplitRankOne B U w) :
    ∃ g : G, Submission.Blueprint.conj g B = P.B ∧ Submission.Blueprint.conj g U = P.U ∧
      MulAut.conj g w = P.w := by
  classical
  obtain ⟨g₀, hg₀⟩ := Work.Models.Abstract.exists_conj_eq P h.stronglyEmbedded
  -- conjugate the datum by `g₀⁻¹` so that its point stabiliser becomes `P.B`
  have h₁ := isSplitRankOne_map (MulAut.conj g₀⁻¹) h
  have hB₁ : B.map (MulAut.conj g₀⁻¹).toMonoidHom = P.B := by
    rw [show B.map (MulAut.conj g₀⁻¹).toMonoidHom = Submission.Blueprint.conj g₀⁻¹ B from rfl,
      hg₀, Work.Models.conj_inv_conj]
  rw [hB₁] at h₁
  obtain ⟨g₁, hg₁B, hg₁U, hg₁w⟩ := datum_conj_eq_general P hstd h₁
  refine ⟨g₁ * g₀⁻¹, ?_, ?_, ?_⟩
  · rw [Work.Models.conj_mul, hg₀, Work.Models.conj_inv_conj]
    exact Work.Models.conj_self_of_mem_normalizer (Subgroup.le_normalizer hg₁B)
  · rw [Work.Models.conj_mul, hg₁U]
  · rw [show MulAut.conj (g₁ * g₀⁻¹) w
        = (MulAut.conj g₁) ((MulAut.conj g₀⁻¹) w) by rw [map_mul]; rfl]
    exact hg₁w

end Work.PSU3.BenderST
