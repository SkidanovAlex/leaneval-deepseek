/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, the `|K| = 4` case)

# Bender's Case 1: the four involutions outside `H = C_G(X)⟨t⟩` commuting with `z`

In the Bender §3, Case 1 setting (`Work.BSW.Cases.K4.K4Hyp`) let `A = C_G(X)`,
`H = A⟨t⟩` and let `z ∈ H` be an involution whose `H`-centralizer is exactly `⟨z⟩`, i.e.

`C_G(z) ∩ H = ⟨z⟩`.

Then exactly four involutions `u ∉ H` commute with `z`.

The reason is a counting one.  By `K4Hyp` the centralizer `C = C_G(z)` is a non-abelian group of
order `8` containing a four-group `W`; such a group is dihedral of order `8` and has exactly five
involutions.  The only one of them lying in `H` is `z` itself, because `C ∩ H = ⟨z⟩` and `⟨z⟩`
contains a single involution.  Hence `5 - 1 = 4` involutions of `C` lie outside `H`.
-/
import Mathlib
import Submission.Work.BSW.Cases.K4.case1Aux
import Submission.Work.BSW.Cases.K4.card_involutions_of_card_eight

namespace Work.BSW.Cases.K4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- A non-abelian subgroup `S` of order `8` containing an elementary abelian subgroup `W` of order
`4` has exactly five involutions.  This is the subgroup form of
`Work.BSW.Cases.K4.card_involutions_of_card_eight`: a non-abelian group of order `8` is dihedral
of order `8` (the four-group `W` rules out the quaternion group), and the dihedral group of order
`8` has five involutions. -/
theorem ncard_involutions_card_eight_le (S : Subgroup G) (hcard : Nat.card ↥S = 8)
    (hnonab : ¬ IsMulCommutative ↥S)
    (W : Subgroup G) (hWle : W ≤ S) (hW4 : Nat.card ↥W = 4)
    (hWsq : ∀ w ∈ W, w * w = 1) :
    ({x : G | x ∈ S ∧ orderOf x = 2} : Set G).ncard = 5 := by
  have hcard' : Nat.card ↥(W.subgroupOf S) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWle).toEquiv, hW4]
  have hsq : ∀ w ∈ W.subgroupOf S, w * w = 1 := by
    intro w hw
    apply Subtype.ext
    simpa using hWsq (w : G) (Subgroup.mem_subgroupOf.mp hw)
  have h5 := card_involutions_of_card_eight hcard hnonab (W.subgroupOf S) hcard' hsq
  have himg : (Subtype.val '' {x : ↥S | orderOf x = 2}) = {x : G | x ∈ S ∧ orderOf x = 2} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
    · rintro ⟨hyS, hy2⟩
      refine ⟨⟨y, hyS⟩, ?_, rfl⟩
      show orderOf (⟨y, hyS⟩ : ↥S) = 2
      rw [← Subgroup.orderOf_coe]
      exact hy2
  rw [← himg, Set.ncard_image_of_injective _ (fun a b h => Subtype.ext h), h5]

theorem case1H_four_partners {G : Type} [Group G] [Finite G] (h : Work.BSW.Cases.K4.K4Hyp G)
    (X : Subgroup G) (t : G) {z : G} (hzH : z ∈ Work.BSW.Cases.K4.case1H X t)
    (hz2 : orderOf z = 2)
    (hCz : Subgroup.centralizer ({z} : Set G) ⊓ Work.BSW.Cases.K4.case1H X t = Subgroup.zpowers z) :
    ({u : G | u ∉ Work.BSW.Cases.K4.case1H X t ∧ orderOf u = 2 ∧ z * u = u * z} : Set G).ncard = 4 := by
  classical
  -- `C = C_G(z)` is non-abelian of order `8` and contains a four-group; hence it has `5`
  -- involutions.
  obtain ⟨W, hWle, hWV4⟩ := h.2.2.2.1 z hz2
  have h5 : ({x : G | x ∈ cent G z ∧ orderOf x = 2} : Set G).ncard = 5 :=
    ncard_involutions_card_eight_le (cent G z) (h.2.1 z hz2) (h.2.2.1 z hz2)
      W hWle hWV4.1 hWV4.2
  set T : Set G := {u : G | u ∉ case1H X t ∧ orderOf u = 2 ∧ z * u = u * z} with hT
  set S : Set G := {x : G | x ∈ cent G z ∧ orderOf x = 2} with hS
  change T.ncard = 4
  have h5' : S.ncard = 5 := by rw [hS]; exact h5
  -- The involutions of `C_G(z)` are `z` together with the required set.
  have hSz : S = insert z T := by
    ext y
    rw [hS, hT, Set.mem_insert_iff]
    constructor
    · intro hy
      obtain ⟨hyC, hy2⟩ := hy
      have hycomm : y * z = z * y :=
        (Subgroup.mem_centralizer_singleton_iff (g := z) (k := y)).mp hyC
      by_cases hyH : y ∈ case1H X t
      · -- `y ∈ C_G(z) ∩ H = ⟨z⟩`, and the only involution of `⟨z⟩` is `z`.
        have hmem : y ∈ Subgroup.zpowers z := by rw [← hCz]; exact ⟨hyC, hyH⟩
        rcases mem_zpowers_eq_one_or hz2 hmem with h1 | h1
        · exact absurd (h1 ▸ hy2) (by simp)
        · exact Or.inl h1
      · exact Or.inr ⟨hyH, hy2, hycomm.symm⟩
    · intro hy
      rcases hy with h | ⟨hyH, hy2, hycomm⟩
      · rw [h]
        exact ⟨(Subgroup.mem_centralizer_singleton_iff (g := z) (k := z)).mpr rfl, hz2⟩
      · exact ⟨(Subgroup.mem_centralizer_singleton_iff (g := z) (k := y)).mpr hycomm.symm, hy2⟩
  have hzT : z ∉ T := by
    rw [hT]
    exact fun hz => hz.1 hzH
  have hmain : S.ncard = T.ncard + 1 := by
    rw [hSz, Set.ncard_insert_of_notMem hzT]
  omega

end Work.BSW.Cases.K4
