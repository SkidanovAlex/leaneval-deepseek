import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.NcardInvSetLeRelIndexInf

set_option linter.style.haveILetI false

namespace Work.CORE3

/-! ## Relative-index lemmas for a tower `W ≤ D ⊔ W ≤ Hh`

These two general subgroup lemmas are the index-theoretic content of `Case1bDStructure`: with
`W = O₂(Ĥ) · O(Ĥ) ⊴ Ĥ` of index `6` and `D = Ĥ ⊓ Ĥ^y`, they turn the inequality
`|I_Ĥ(y)| ≤ |D : D ⊓ W|` into the equation `|D : D ⊓ W| = 6` and then into `D · W = Ĥ`. -/

/-- For subgroups `D ≤ Hh` and `W ≤ Hh` of `G` with `W` normal in `Hh` (that is,
`(W.subgroupOf Hh).Normal`), the index of `W` in `D ⊔ W` equals the index of `W ⊓ D` in `D`.
This is the second isomorphism theorem `D/(D ⊓ W) ≅ D·W/W` phrased in `relIndex` terms.  It is
transferred to the group `↥Hh`, where `W.subgroupOf Hh` is normal, using
`Subgroup.relIndex_sup_right` and `Subgroup.relIndex_subgroupOf`. -/
theorem relIndex_sup_eq_inf_relIndex {G : Type} [Group G] (Hh W D : Subgroup G)
    (hWle : W ≤ Hh) (hDle : D ≤ Hh) (hWn : (W.subgroupOf Hh).Normal) :
    W.relIndex (D ⊔ W) = (W ⊓ D).relIndex D := by
  haveI : (W.subgroupOf Hh).Normal := hWn
  have h := Subgroup.relIndex_sup_right (D.subgroupOf Hh) (W.subgroupOf Hh)
  rw [← Subgroup.subgroupOf_sup hDle hWle] at h
  rw [Subgroup.relIndex_subgroupOf (H := W) (L := Hh) (sup_le hDle hWle)] at h
  rw [Subgroup.relIndex_subgroupOf (H := W) (L := Hh) hDle] at h
  rw [Subgroup.inf_relIndex_right]
  exact h

/-- Converse direction: if `|D : D ⊓ W| = |Hh : W| ≠ 0` then `D ⊔ W = Hh`.  Indeed
`W.relIndex (D ⊔ W) = (W ⊓ D).relIndex D = W.relIndex Hh` and `relIndex` is multiplicative in
the tower `W ≤ D ⊔ W ≤ Hh`, so `(D ⊔ W).relIndex Hh = 1`. -/
theorem sup_eq_of_inf_relIndex_eq {G : Type} [Group G] (Hh W D : Subgroup G)
    (hWle : W ≤ Hh) (hDle : D ≤ Hh) (hWn : (W.subgroupOf Hh).Normal)
    (hne : W.relIndex Hh ≠ 0) (heq : (W ⊓ D).relIndex D = W.relIndex Hh) :
    D ⊔ W = Hh := by
  have h1 := relIndex_sup_eq_inf_relIndex Hh W D hWle hDle hWn
  have h2 := Subgroup.relIndex_mul_relIndex (H := W) (K := D ⊔ W) (L := Hh)
    le_sup_right (sup_le hDle hWle)
  rw [heq] at h1
  rw [h1] at h2
  have h3 : (D ⊔ W).relIndex Hh = 1 := by
    refine Nat.mul_left_cancel (Nat.pos_of_ne_zero hne) ?_
    rw [mul_one]
    exact h2
  exact le_antisymm (sup_le hDle hWle) (Subgroup.relIndex_eq_one.mp h3)

/-- Bender 1981 §3, p. 223–224 (`Submission/Work/lead_gw_prior/_bender3.txt`).  Setting: `G` a
minimal counterexample (`BenderCtx`), `B` a Bender setup, `Case1 B`, `V = O₂(Ĥ)` of type `(2,2)`
(`Case1bData B`), `U = O(Ĥ)`, `VU = V ⊔ U`, `VU ⊴ Ĥ`, `|Ĥ : VU| = 6`.

For an involution `y ∉ Ĥ` whose coset `yĤ` carries at least four involutions (`4 ≤
cosetInvCount Ĥ y`), put `D := Ĥ ⊓ Ĥ^y`.  Then `D · VU = Ĥ`, so `D/(D ⊓ VU) ≅ S₃` has order `6`,
and the inverted set of `y` in `Ĥ` lies in `D`. -/
theorem Case1bDStructure (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → 4 ≤ Work.GW2.cosetInvCount B.Hhat y →
      (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) ⊔ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) = B.Hhat ∧
      ((Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) ⊓
          (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)).relIndex
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) = 6 ∧
      invSetIn B.Hhat y ⊆ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := by
  intro y hy2 hyH h4c
  -- `y` is an involution
  have hy : y * y = 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).1
  -- the index `d = |D : D ⊓ VU|`
  set d : ℕ := ((Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) ⊓
      (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)).relIndex
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) with hd
  -- the inverted set of `y` in `Ĥ` lies in `D = Ĥ ⊓ Ĥ^y`
  have hsub : invSetIn B.Hhat y ⊆ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := by
    intro x hx
    obtain ⟨hxH, hxy⟩ := hx
    refine ⟨hxH, ?_⟩
    change x ∈ Work.GW2.conjSub y B.Hhat
    rw [Work.CORE2A.mem_conjSub_iff]
    have h1 : y⁻¹ * x * y = x⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hy]
      exact hxy
    rw [h1]
    exact B.Hhat.inv_mem hxH
  -- the structural facts about `VU = O₂(Ĥ) ⊔ O(Ĥ)`
  have hWle : Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U ≤ B.Hhat := by
    have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft hBc B
    exact sup_le (Work.CORE2A.thm26Concl_O2_le_Hhat h26)
      (Work.CORE2A.thm26Concl_U_le_Hhat h26)
  have hDle : B.Hhat ⊓ Work.GW2.conjSub y B.Hhat ≤ B.Hhat := inf_le_left
  have hWn : ((Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).subgroupOf B.Hhat).Normal :=
    normal_VU_subgroupOf G I hBc B h1 D
  have h6 : (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 :=
    relIndex_VU_Hhat G I hBc B h1 D
  -- Bender's (5) for `VU`
  have h5 : ∀ z : G, z * z = 1 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1} := by
    intro z hz hzH
    refine InvSetVUSingleton G I hBc B h1 D z ?_ hzH
    exact (orderOf_eq_two_iff_mul_self z).mpr
      ⟨hz, fun h1z => hzH (by rw [h1z]; exact B.Hhat.one_mem)⟩
  have hcount : (invSetIn B.Hhat y).ncard = Work.GW2.cosetInvCount B.Hhat y :=
    ncard_invSetIn_eq_cosetInvCount B.Hhat y hy hyH
  -- the counting bound `|I_Ĥ(y)| ≤ d`
  have hbound : (invSetIn B.Hhat y).ncard ≤ d := by
    rw [hd]
    exact NcardInvSetLeRelIndexInf B.Hhat (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U)
      (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) hWle hDle hWn h5 hy hyH hsub
  have hge : 4 ≤ d := by
    rw [hcount] at hbound
    exact le_trans h4c hbound
  -- `d` divides `|Ĥ : VU| = 6`, since `d = W.relIndex (D ⊔ W)` and `relIndex` is multiplicative
  have hdvd : d ∣ 6 := by
    rw [hd, ← h6]
    have h2 := Subgroup.relIndex_mul_relIndex (H := Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U)
      (K := (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) ⊔ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U))
      (L := B.Hhat) le_sup_right (sup_le hDle hWle)
    rw [relIndex_sup_eq_inf_relIndex B.Hhat (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U)
      (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) hWle hDle hWn] at h2
    exact ⟨_, h2.symm⟩
  have hd6 : d = 6 := by
    have hle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases d
    · norm_num at hdvd
    · norm_num at hdvd
    · rfl
  refine ⟨?_, hd6, hsub⟩
  refine sup_eq_of_inf_relIndex_eq B.Hhat (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U)
    (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) hWle hDle hWn ?_ ?_
  · rw [h6]; norm_num
  · rw [← hd, hd6, h6]

end Work.CORE3
