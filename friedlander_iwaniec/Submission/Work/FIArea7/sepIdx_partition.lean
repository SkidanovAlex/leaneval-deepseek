/-
# `Submission.Work.FIArea7.sepIdx_partition`

The three index sets `dIdx`, `mIdx`, `nIdx` of the *FI* §24 separation triple partition the
set of prime positions `Fin k`: every position lies in exactly one of the three sets.

Write the 1-based position as `v = i.val + 1 = r * q + s` with `0 ≤ s < r` (so `q = v / r`,
`s = v % r`).  Then (`SepDiv.lean`)

* `dIdx` contains the positions with `v ≤ r` (the whole first block) and those with `s = 0`,
  `v ≥ 2r`;
* `mIdx` contains the positions with `s ≠ 0` and `q` odd;
* `nIdx` contains the positions with `s ≠ 0`, `q` even and `q > 0`.

Hence every position falls in exactly one set: if `v ≤ r` it is in `dIdx`; otherwise `q ≥ 1`,
and either `s = 0` (whence `q ≥ 2`, so the position is in `dIdx`), or `s ≠ 0`, in which case `q`
is odd (`mIdx`) or even (`nIdx`).  The sets are pairwise disjoint because the corresponding
conditions on `(s, q)` are mutually exclusive.
-/
import Mathlib
import Submission.Work.FIArea7.SepDiv
import Submission.Work.FIArea7.sepPair_bounds

set_option autoImplicit false

namespace Work.FIArea7

open Finset

theorem sepIdx_partition (r k : ℕ) (hr : 2 ≤ r) :
    dIdx r k ∪ mIdx r k ∪ nIdx r k = Finset.univ ∧
      Disjoint (dIdx r k) (mIdx r k) ∧ Disjoint (dIdx r k) (nIdx r k) ∧
        Disjoint (mIdx r k) (nIdx r k) := by
  have hr0 : 0 < r := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- **Covering:** every position is in one of the three sets.
    rw [Finset.eq_univ_iff_forall]
    intro i
    rw [Finset.mem_union, Finset.mem_union]
    by_cases hlt : i.val < r
    · -- first block: `dIdx`
      exact Or.inl (Or.inl (by rw [mem_dIdx]; exact Or.inl hlt))
    · have hge : r ≤ i.val := by omega
      have hqpos : 0 < (i.val + 1) / r := Nat.div_pos (by omega) hr0
      by_cases hs : (i.val + 1) % r = 0
      · -- `s = 0` and `v > r` forces `q ≥ 2`: `dIdx`
        refine Or.inl (Or.inl ?_)
        rw [mem_dIdx]
        right
        have hdecomp := Nat.div_add_mod (i.val + 1) r
        have hrv : r * ((i.val + 1) / r) = i.val + 1 := by omega
        have hqne1 : (i.val + 1) / r ≠ 1 := by
          intro h; rw [h, Nat.mul_one] at hrv; omega
        have h2 : 2 ≤ (i.val + 1) / r := by omega
        refine ⟨hs, ?_⟩
        calc 2 * r = r * 2 := by ring
          _ ≤ r * ((i.val + 1) / r) := Nat.mul_le_mul_left r h2
          _ = i.val + 1 := hrv
      · -- `s ≠ 0`: split on the parity of `q`
        have hs0 : 0 < (i.val + 1) % r := Nat.pos_of_ne_zero hs
        have hmod2 : (i.val + 1) / r % 2 = 0 ∨ (i.val + 1) / r % 2 = 1 := by
          have := Nat.mod_lt ((i.val + 1) / r) (show 0 < 2 by norm_num)
          omega
        rcases hmod2 with h | h
        · exact Or.inr (by rw [mem_nIdx]; exact ⟨hs0, h, hqpos⟩)
        · exact Or.inl (Or.inr (by rw [mem_mIdx]; exact ⟨hs0, h⟩))
  · -- **`dIdx` and `mIdx` are disjoint.**
    rw [Finset.disjoint_left]
    intro i hd hm
    rw [mem_dIdx] at hd
    rw [mem_mIdx] at hm
    obtain ⟨hs0, hqo⟩ := hm
    rcases hd with hlt | ⟨hmod0, -⟩
    · have hv : i.val + 1 ≤ r := by omega
      have hsq : (i.val + 1) / r ≤ 1 := by
        have hle : (i.val + 1) / r ≤ r / r := Nat.div_le_div_right hv
        rwa [Nat.div_self hr0] at hle
      have hq1 : (i.val + 1) / r = 1 := by
        rcases Nat.eq_zero_or_pos ((i.val + 1) / r) with h | h
        · rw [h] at hqo; simp at hqo
        · omega
      have hdecomp := Nat.div_add_mod (i.val + 1) r
      rw [hq1, Nat.mul_one] at hdecomp
      omega
    · rw [hmod0] at hs0; omega
  · -- **`dIdx` and `nIdx` are disjoint.**
    exact disjoint_dIdx_nIdx r k
  · -- **`mIdx` and `nIdx` are disjoint:** `q` cannot be both odd and even.
    rw [Finset.disjoint_left]
    intro i hm hn
    rw [mem_mIdx] at hm
    rw [mem_nIdx] at hn
    obtain ⟨-, hqo⟩ := hm
    obtain ⟨-, hqe, -⟩ := hn
    omega

end Work.FIArea7
