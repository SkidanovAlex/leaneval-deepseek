import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ZassenhausSuzuki.QSZ_invH_le_centerQ
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `SzHyp`: the hypotheses of Suzuki 1962 §8, without `Situation`

The Peterfalvi Ch. V §2 chain (`Work.ThmF.ChV12.L5Struct`, `...X5RankOneAux`,
`...L5simpleX5`, `...L5zassenhaus`, `...lemma5a`, `...X5_rankOne_of`) is stated for the
structure `Work.ThmF.Lemma5.Hyp5`, whose first field is `Situation G` = (B0) + (B1) + (B2).
In the setting of `Work.ZassenhausSuzuki.Q_suzuki_sq` the group is *only* assumed simple, so
`Situation G` (in particular the induction hypothesis `ThmBBelow (Nat.card G)`) is not
available.

This file records the weaker hypothesis bundle that *is* available there, together with the
facts that the chain extracts from `Situation G`:

* `invH_commute` in place of `Work.ThmF.L5.involutions_commute` (Ch. V §1 Prop. 1 (c));
* `Ksub H t = Kset H t` in place of `Work.ThmF.ChV12.Ksub_cyclic_normal` /
  `Work.ThmF.ChV12.L5prop2` (Ch. V §1 Prop. 2);
* `HasFourGroup G` in place of `Situation G .1.1`.

The shadow copies of the chain live in `Submission/Work/ZassenhausSuzuki/Shadow/`, keep the
original names and namespaces, and import this module.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-- The hypotheses under which Suzuki 1962, §8 (`σ = ρ` ⟹ `G ≃ LF(2,q)`) is applied in the
`ZassenhausSuzuki` area: a split rank-one Zassenhaus datum with `Q` a `2`-group and a
distinguished involution `s ∈ Q` with `(s * t) ^ 3 = 1`, plus the four-group of (B0). -/
structure SzHyp (H Q : Subgroup G) (t s : G) : Prop where
  split : IsSplitRankOne H Q t
  zass : IsZassenhaus H
  two : IsPGroup 2 Q
  four : HasFourGroup G
  s_mem : s ∈ Q
  s_inv : orderOf s = 2
  ord3 : orderOf (s * t) = 3

namespace SzHyp

/-- Ch. V §1 Prop. 1 (c): the involutions of `H` commute. -/
theorem hcomm (h : SzHyp H Q t s) :
    ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G), a * b = b * a := by
  intro u hu v hv
  have hu' := Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h.split h.two u hu)
  have hv' := Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h.split h.two v hv)
  exact hu'.2 v hv'.1

/-- `Q ≠ ⊥` (`s ∈ Q` has order two). -/
theorem Q_ne_bot (h : SzHyp H Q t s) : Q ≠ ⊥ := by
  intro hbot
  have hs1 : s = 1 := by simpa using (Subgroup.mem_bot.mp (hbot ▸ h.s_mem))
  have hs2 : orderOf s = 2 := h.s_inv
  rw [hs1, orderOf_one] at hs2
  exact absurd hs2 (by norm_num)

/-- `Kset H t = D = twoPoint H t` (Zassenhaus case): `Kset ⊆ twoPoint` is immediate, and
`twoPoint ⊆ Kset` is `t` inverting the two-point stabiliser (`t_conj_eq_inv`). -/
theorem Kset_eq_twoPoint (h : SzHyp H Q t s) :
    Work.ThmF.Kset H t = (twoPoint H t : Set G) := by
  have htinv : t⁻¹ = t := by
    have h1 := pow_orderOf_eq_one t
    rw [h.split.invol] at h1
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h1)
  ext x
  rw [Work.ThmF.mem_Kset_iff]
  exact ⟨fun hx => hx.1,
    fun hx => ⟨hx, by
      rw [htinv]
      exact Work.ZassenhausPSL2.ZData.t_conj_eq_inv H Q t h.split h.zass
        h.Q_ne_bot h.two x hx⟩⟩

/-- Ch. V §1 Prop. 2: `K = J(D,t)` is a subgroup (`Ksub H t = Kset H t`), in the Zassenhaus
case, where in fact `Ksub H t = twoPoint H t`. -/
theorem Ksub_eq_twoPoint (h : SzHyp H Q t s) :
    (Work.ThmF.Ksub H t : Set G) = (twoPoint H t : Set G) := by
  have h1 : Work.ThmF.Ksub H t = twoPoint H t := by
    rw [Work.ThmF.Ksub, Kset_eq_twoPoint h, Subgroup.closure_eq]
  rw [h1]

theorem Ksub_eq_Kset (h : SzHyp H Q t s) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := by
  rw [Ksub_eq_twoPoint h, ← Kset_eq_twoPoint h]

/-- The elementary consequence of `orderOf (s * t) = 3` (Ch. V §2 Lemma 5). -/
theorem tst_eq_sts (h : SzHyp H Q t s) : t * s * t = s * t * s := by
  have hss : s * s = 1 := by
    have h1 := pow_orderOf_eq_one s
    rw [h.s_inv] at h1
    simpa [pow_two] using h1
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.split.invol] at h1
    simpa [pow_two] using h1
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h3 : (s * t) ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one (s * t)
    rw [h.ord3] at h1
    exact h1
  have h3' : (s * t) * ((s * t) * (s * t)) = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using h3
  have hsq : (s * t) * (s * t) = t * s := by
    have h8 : (s * t) * (s * t) = (s * t)⁻¹ := by
      have h10 := congrArg (fun z => z * (s * t)⁻¹) h3'
      simpa [mul_assoc] using h10
    rw [h8, mul_inv_rev, hsinv, htinv]
  have h9 : s * (t * s * t) = s * (s * t * s) := by
    rw [show s * (t * s * t) = (s * t) * (s * t) by group, hsq]
    rw [show s * (s * t * s) = (s * s) * (t * s) by group, hss, one_mul]
  exact mul_left_cancel h9

/-- `Kset H t` contains a non-identity element (`D = H ⊓ H^t` has odd order `≠ 1`). -/
theorem exists_Kset_ne_one (h : SzHyp H Q t s) :
    ∃ x : G, x ∈ Work.ThmF.Kset H t ∧ x ≠ 1 := by
  have hcard := Work.ThmF.Bender.cardKsetEqInv h.split.stronglyEmbedded h.split.invol
    h.split.not_mem
  have hgt : 1 < (Work.ThmF.Kset H t).ncard := by
    rw [hcard]
    exact lt_of_lt_of_le (by norm_num)
      (Work.ThmF.Bender.cardInvGeTwo h.split.stronglyEmbedded h.four)
  obtain ⟨x, hx, hx1⟩ := Set.exists_ne_of_one_lt_ncard hgt 1
  exact ⟨x, hx, hx1⟩

end SzHyp

end Work.ZassenhausSuzuki
