import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BMF.N7

open Finset

/-- The dyadic blocks `Ioc (2^j) (min (2^(j+1)) N)`, `j ∈ range J`, are pairwise disjoint. -/
private lemma pairwiseDisjoint_Ioc_dyadic (N J : ℕ) :
    (Finset.range J : Set ℕ).PairwiseDisjoint
      (fun j => Finset.Ioc (2 ^ j) (Nat.min (2 ^ (j + 1)) N)) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro i _ j _ hne
  obtain ⟨x, hx⟩ := hne
  rw [Finset.mem_inter, Finset.mem_Ioc, Finset.mem_Ioc] at hx
  obtain ⟨⟨h1i, h2i⟩, h1j, h2j⟩ := hx
  by_contra hij
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt h)
    have hmin : Nat.min (2 ^ (i + 1)) N ≤ 2 ^ (i + 1) := Nat.min_le_left _ _
    omega
  · have hle : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt h)
    have hmin : Nat.min (2 ^ (j + 1)) N ≤ 2 ^ (j + 1) := Nat.min_le_left _ _
    omega

/-- The dyadic blocks `Ioc (2^j) (min (2^(j+1)) N)`, `j ∈ range J`, cover `Ioc 1 N`
whenever `N ≤ 2^J`. -/
private lemma biUnion_Ioc_dyadic (N J : ℕ) (hJ : N ≤ 2 ^ J) :
    (Finset.range J).biUnion (fun j => Finset.Ioc (2 ^ j) (Nat.min (2 ^ (j + 1)) N))
      = Finset.Ioc 1 N := by
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hx⟩
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Ioc] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    have hmin : Nat.min (2 ^ (j + 1)) N ≤ N := Nat.min_le_right _ _
    have hle : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
    omega
  · intro hx
    rw [Finset.mem_Ioc] at hx
    obtain ⟨h1, h2⟩ := hx
    have hx1 : x - 1 ≠ 0 := by omega
    refine ⟨Nat.log 2 (x - 1), ?_, ?_⟩
    · rw [Finset.mem_range]
      by_contra h
      rw [Nat.not_lt] at h
      have hple : 2 ^ Nat.log 2 (x - 1) ≤ x - 1 := Nat.pow_log_le_self 2 hx1
      have h2J : 2 ^ J ≤ 2 ^ Nat.log 2 (x - 1) := Nat.pow_le_pow_right (by norm_num) h
      omega
    · rw [Finset.mem_Ioc]
      have hple : 2 ^ Nat.log 2 (x - 1) ≤ x - 1 := Nat.pow_log_le_self 2 hx1
      have hplt : x - 1 < 2 ^ (Nat.log 2 (x - 1)).succ :=
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (x - 1)
      constructor
      · omega
      · apply le_min
        · omega
        · omega

/-- Dyadic decomposition of `(1, N]`: for `1 ≤ J` and `N ≤ 2^J`, the interval `Ioc 1 N` is the
disjoint union of the blocks `Ioc (2^j) (min (2^(j+1)) N)`, `j ∈ range J`.

Suggested imports: `import Mathlib`.

Route: `Finset.sum_biUnion` with `s = Finset.range J` and `t j = Finset.Ioc (2^j) (min (2^(j+1)) N)`.
Pairwise disjointness holds because `Ioc (2^j) (min (2^(j+1)) N) ⊆ Ioc (2^j) (2^(j+1))` and these
are disjoint for distinct `j`. For the union: given `x` with `1 < x ≤ N`, take
`j := Nat.log 2 (x - 1)`; then `2^j ≤ x - 1 < 2^(j+1)` (Mathlib: `Nat.pow_log_le_self`,
`Nat.lt_pow_succ_log_self`), so `2^j < x ≤ 2^(j+1)`, and `j < J` because `2^j < x ≤ N ≤ 2^J`. -/
theorem sum_Ioc_dyadic_eq_range (f : ℕ → ℂ) (N J : ℕ) (hJ : N ≤ 2 ^ J) (hJ1 : 1 ≤ J) :
    ∑ n ∈ Finset.Ioc 1 N, f n
      = ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2 ^ j) (Nat.min (2 ^ (j + 1)) N), f n := by
  rw [← biUnion_Ioc_dyadic N J hJ]
  exact Finset.sum_biUnion (pairwiseDisjoint_Ioc_dyadic N J)

end Work.BMF.N7
