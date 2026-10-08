import Mathlib
import Submission.Work.Models.Port.BenderSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.Abstract.eq_mul_w_of_mem_normalizer`

For a Bender pair `P` with `P.w * P.w = 1`, every element of `N_G(T) \ B` is of the form
`d * P.w` with `d ∈ P.T`.

`normalizer_T` gives `N_G(T) = T ⊔ ⟨w⟩`; since `w` normalises `T`, the sup is the product set
`T · ⟨w⟩` (`Subgroup.coe_mul_of_right_le_normalizer_left`), so `s = d * z` with `d ∈ T`,
`z ∈ ⟨w⟩`.  Writing `z = w ^ k` and using `w ^ 2 = 1` (`zpow_eq_zpow_emod`) reduces `z` to
`1` or `w`: `z = 1` puts `s = d ∈ T ≤ B`, against `s ∉ B`, while `z = w` is the claim.
-/

open Pointwise

namespace Work.Models.Abstract

theorem eq_mul_w_of_mem_normalizer {G : Type*} [Group G] [Finite G]
    (P : Submission.BenderPair G) (hww : P.w * P.w = 1) {s : G}
    (hs : s ∈ Subgroup.normalizer (P.T : Set G)) (hsB : s ∉ P.B) :
    ∃ d ∈ P.T, s = d * P.w := by
  -- `N_G(T) = T ⊔ ⟨w⟩`, and `w ∈ N_G(T)`, so the sup is the product set `T · ⟨w⟩`.
  rw [P.normalizer_T] at hs
  have hcoe : ((P.T ⊔ Subgroup.zpowers P.w : Subgroup G) : Set G)
      = (P.T : Set G) * (Subgroup.zpowers P.w : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P.T (Subgroup.zpowers P.w)
      (Subgroup.zpowers_le.mpr P.hwT)
  have hs' : s ∈ ((P.T ⊔ Subgroup.zpowers P.w : Subgroup G) : Set G) := hs
  rw [hcoe, Set.mem_mul] at hs'
  obtain ⟨d, hd, z, hz, hdz⟩ := hs'
  -- `z = w ^ k` for some `k : ℤ`, and `w ^ 2 = 1` reduces this to `z = 1` or `z = w`.
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hw2 : P.w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hww
  have hred : P.w ^ k = P.w ^ (k % 2) := zpow_eq_zpow_emod k (n := (2 : ℤ)) hw2
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · -- `z = 1`, so `s = d ∈ T ≤ B`, contradicting `s ∉ B`.
    exfalso
    have hz1 : z = 1 := by rw [← hk, hred, h0, zpow_zero]
    have hsd : s = d := by rw [← hdz, hz1, mul_one]
    have : s ∈ P.B := by rw [hsd]; exact P.T_le_B hd
    exact hsB this
  · -- `z = w`, so `s = d * w`.
    have hz1 : z = P.w := by rw [← hk, hred, h1, zpow_one]
    exact ⟨d, hd, by rw [← hdz, hz1]⟩

end Work.Models.Abstract
