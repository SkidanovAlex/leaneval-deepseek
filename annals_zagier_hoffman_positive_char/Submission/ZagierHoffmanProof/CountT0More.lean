/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.CountT0
import Submission.ZagierHoffmanProof.DBound
import Submission.ZagierHoffmanProof.ShuffleSpan

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators Pointwise

/-!
# `𝒯0` versus `𝒯` in the range `w ≤ q`

The paper observes that *for `w ≤ q` the sets `𝒯0_w` and `𝒯_w` coincide* (this is why the algebraic
part of Theorem A is trivial in that range).  We prove it:

  ★★ `T0_eq_T_of_le {w} (hw : w ≤ Nat.card F) : 𝒯0 F w = 𝒯 F w`

together with the counting consequences

  ★★ `hoffCount0_eq_d_of_le (1 ≤ w ≤ q) : hoffCount0 F w = d F w`
  ★★ `hoffCount0_le_two_pow (1 ≤ w) : hoffCount0 F w ≤ 2^{w-1}`
      (via `ncard 𝒯0_w ≤ d w`, Theorem A's counting, and `d_le_two_pow`).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- In a weight-`w ≤ q` tuple whose last entry is `< q`, *every* entry is `< q`.  This is the
paper's observation that `𝒯0_w = 𝒯_w` for `w ≤ q`. -/
lemma entry_lt_card_of_le {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) {w : ℕ} (hw : w ≤ Nat.card F)
    (hsum : (∑ i : Fin r, (𝔰 i : ℕ)) = w)
    (hlast : (𝔰 ⟨r - 1, by omega⟩ : ℕ) < Nat.card F) (i : Fin r) :
    (𝔰 i : ℕ) < Nat.card F := by
  by_cases hi : i = ⟨r - 1, by omega⟩
  · rw [hi]
    exact hlast
  · -- a non-last entry: the other `r - 1 ≥ 1` entries are all at least `1`
    have hcard : (Finset.univ.erase i).card = r - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hge : r - 1 ≤ ∑ j ∈ Finset.univ.erase i, (𝔰 j : ℕ) := by
      have h1 : ∑ j ∈ Finset.univ.erase i, (1 : ℕ) ≤ ∑ j ∈ Finset.univ.erase i, (𝔰 j : ℕ) :=
        Finset.sum_le_sum (fun j _ => (𝔰 j).pos)
      have h2 : ∑ j ∈ Finset.univ.erase i, (1 : ℕ) = (Finset.univ.erase i).card := by simp
      omega
    have hsplit : (∑ j : Fin r, (𝔰 j : ℕ))
        = (𝔰 i : ℕ) + ∑ j ∈ Finset.univ.erase i, (𝔰 j : ℕ) := by
      rw [← Finset.sum_erase_add (Finset.univ) (fun j : Fin r => (𝔰 j : ℕ))
        (Finset.mem_univ i), add_comm]
    have hri : 1 ≤ r - 1 := by
      have := i.isLt
      have hne : (i : ℕ) ≠ r - 1 := fun h => hi (Fin.ext h)
      omega
    have hmain : (𝔰 i : ℕ) + (r - 1) ≤ w := by omega
    omega


/-- ★★ **The paper's observation `𝒯0_w = 𝒯_w` for `w ≤ q`.**  For weights at most `q` the two
Hoffman-type sets agree: an entry exceeding `q - 1` is impossible because the entries are positive
and the total weight is at most `q`. -/
theorem T0_eq_T_of_le (w : ℕ) (hw : w ≤ Nat.card F) : 𝒯0 F w = 𝒯 F w := by
  refine Set.Subset.antisymm (T0_subset_T F w) ?_
  intro x hx
  rw [𝒯, Set.mem_iUnion] at hx
  obtain ⟨r, hxr⟩ := hx
  rw [mem_𝒯_aux_iff F w r] at hxr
  obtain ⟨𝔰, h𝔰, _, hlast, rfl⟩ := hxr
  rw [𝒯0, Set.mem_iUnion]
  refine ⟨r, ?_⟩
  rw [mem_𝒯0_aux_iff F w r]
  exact ⟨𝔰, h𝔰, fun i => entry_lt_card_of_le F r.pos 𝔰 hw h𝔰 (by simpa using hlast) i, rfl⟩

/-- ★★ **The exact count for `w ≤ q`**: `d₀(w) = |𝒯0_w| = |𝒯_w| = d(w)`. -/
theorem hoffCount0_eq_d_of_le {w : ℕ} (hw1 : 1 ≤ w) (hwq : w ≤ Nat.card F) :
    hoffCount0 F w = d F w := by
  rw [← ncard_T0_eq_hoffCount0 F w hw1, T0_eq_T_of_le F w hwq, ncard_T_eq_d F w hw1]

/-- ★★ **The counting bound for `𝒯0`**: `|𝒯0_w| ≤ 2^{w-1}` (via `|𝒯0_w| ≤ d(w) ≤ 2^{w-1}`). -/
theorem hoffCount0_le_two_pow {w : ℕ} (hw : 1 ≤ w) : hoffCount0 F w ≤ 2 ^ (w - 1) := by
  rw [← ncard_T0_eq_hoffCount0 F w hw]
  exact le_trans (ncard_T0_le_d F w hw) (d_le_two_pow F w hw)

/-- ★★ Sanity: below the threshold the two counts agree, `|𝒯0_w| = d(w)`. -/
theorem ncard_T0_eq_ncard_T_of_le {w : ℕ} (hw : w ≤ Nat.card F) :
    Set.ncard (𝒯0 F w) = Set.ncard (𝒯 F w) := by
  rw [T0_eq_T_of_le F w hw]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

/-- Over `F₃`: `|𝒯0_3| = d(3) = 3` (all entries `< 3`, weight `3`). -/
example : hoffCount0 (ZMod 3) 3 = 3 := by
  have hq : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hoffCount0_eq_d_of_le (ZMod 3) (by norm_num) (by rw [hq])]
  have h := d_eq_pow_two_sub_one (ZMod 3)
  rw [hq] at h
  norm_num at h
  exact h

/-- Over `F₂`: `|𝒯0_w| ≤ 2^{w-1}`. -/
example : hoffCount0 (ZMod 2) 5 ≤ 16 := by
  have h := hoffCount0_le_two_pow (ZMod 2) (w := 5) (by norm_num)
  norm_num at h
  exact h

end ZagierHoffmanPositiveChar
