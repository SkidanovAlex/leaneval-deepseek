import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.NormalizerPcoreEqHhat

/-!
# Bender 1981 §3 (5) ⟹ at most six involutions per coset

Given Bender's (5) — no involution outside `Ĥ` inverts a nontrivial element of `VU = O₂(Ĥ)·O(Ĥ)`
— the inverted set `I_Ĥ(y)` of an involution `y ∉ Ĥ` maps injectively into `Ĥ/VU`, which has
order `6`.  Hence the coset `yĤ` contains at most six involutions.

The file also records the two structural facts about `VU` used by the later leaves:
`VU ⊴ Ĥ` and `|Ĥ : VU| = 6`.
-/

namespace Work.CORE3

open Work.GW2
open Subgroup

variable {G : Type} [Group G]

/-- The image of a normal subgroup of `↥K` under the subtype map is normal in `K`.  (Local copy
of the elementary observation used in `InvCountHhat`.) -/
private theorem subgroupOf_map_subtype_eq_aux (K : Subgroup G) (L : Subgroup ↥K) :
    (L.map K.subtype).subgroupOf K = L := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx; exact ⟨x, hx, rfl⟩

/-- `VU = O₂(Ĥ) ⊔ O(Ĥ)` is normal in `Ĥ`.  (`O₂(Ĥ) ⊴ Ĥ` and `O(Ĥ) ⊴ Ĥ`.) -/
theorem normal_VU_subgroupOf (G : Type) [Group G] [Finite G] (I : Case1Inputs)
    (h : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) :
    ((pCoreIn 2 B.Hhat ⊔ B.U).subgroupOf B.Hhat).Normal := by
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  have hVle : pCoreIn 2 B.Hhat ≤ B.Hhat := Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hUle : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hVnorm : B.Hhat ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    simpa [pCoreIn] using Work.CORE3.le_normalizer_map_subtype B.Hhat (pCore 2 ↥B.Hhat)
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_oddCore_eq h26]
    simpa [oddCoreIn] using
      Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
  have hWnorm : B.Hhat ≤
      Subgroup.normalizer ((pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G) : Set G) :=
    le_trans (le_inf hVnorm hUnorm)
      (Subgroup.inf_normalizer_le_normalizer_sup (pCoreIn 2 B.Hhat) B.U)
  rw [Subgroup.normal_subgroupOf_iff (sup_le hVle hUle)]
  intro a k ha hk
  exact (Subgroup.mem_normalizer_iff.mp (hWnorm hk) a).mp ha

/-- In the `(2,2)` subcase of Bender's §3, `VU = O₂(Ĥ) ⊔ O(Ĥ)` has index `6` in `Ĥ`. -/
theorem relIndex_VU_Hhat (G : Type) [Group G] [Finite G] (I : Case1Inputs)
    (h : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) :
    (pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 := by
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  rcases h26.2.2 with ⟨hle, -⟩ | ⟨-, h6, -⟩
  · exact absurd (isCyclic_of_le_of_isCyclic' hle B.S0_cyclic)
      (not_isCyclic_of_isFourGroup' D.four)
  · exact h6

/-- **Bender (5) ⟹ `n ≤ 6`.**  If no involution outside `B.Hhat` inverts a nontrivial element of
`VU = O₂(Ĥ) ⊔ O(Ĥ)`, then every coset of `B.Hhat` containing an involution `y ∉ B.Hhat` contains
at most six of them. -/
theorem cosetInvCount_le_six (G : Type) [Group G] [Finite G] (I : Case1Inputs)
    (h : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B)
    (h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      invSet (pCoreIn 2 B.Hhat ⊔ B.U) z = {1}) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → cosetInvCount B.Hhat y ≤ 6 := by
  intro y hy2 hyH
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  have hy : y * y = 1 := (orderOf_eq_two_iff_mul_self y).mp hy2 |>.1
  have h5' : ∀ z : G, z * z = 1 → z ∉ B.Hhat → invSet (pCoreIn 2 B.Hhat ⊔ B.U) z = {1} := by
    intro z hz hzH
    have hz1 : z ≠ 1 := by rintro rfl; exact hzH B.Hhat.one_mem
    exact h5 z ((orderOf_eq_two_iff_mul_self z).mpr ⟨hz, hz1⟩) hzH
  have hWle : pCoreIn 2 B.Hhat ⊔ B.U ≤ B.Hhat :=
    sup_le (Work.CORE2A.thm26Concl_O2_le_Hhat h26) (Work.CORE2A.thm26Concl_U_le_Hhat h26)
  have hbound := ncard_invSetIn_le_relIndex B.Hhat (pCoreIn 2 B.Hhat ⊔ B.U) hWle
    (normal_VU_subgroupOf G I h B h1 D) h5' hy hyH
  rw [relIndex_VU_Hhat G I h B h1 D] at hbound
  rwa [ncard_invSetIn_eq_cosetInvCount B.Hhat y hy hyH] at hbound

end Work.CORE3
