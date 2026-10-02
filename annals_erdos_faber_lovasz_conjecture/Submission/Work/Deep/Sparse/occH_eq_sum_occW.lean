import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.NcpDefs

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Sparse

/-!
# The telescoping identity for the class contribution `occH`

`occH n = C(n,2) - C(n,3)` is the contribution of a colour class of size `n` to the pair
statistic minus the triple statistic, and `occW j = (j-1)(4-j)/2` is its increment,

`occH (j+1) - occH j = occW j`  (`occW_succ` below).

Since `occH 0 = occH 1 = 0`, summing the increments gives the requested identity

`occH n = ∑_{2 ≤ j ≤ n} occW j`.
-/

/-- `occH n = 0` for `n ≤ 1`: both `C(n,2)` and `C(n,3)` vanish. -/
private lemma occH_eq_zero_of_le_one (n : ℕ) (hn : n ≤ 1) : occH n = 0 := by
  have h2 : n.choose 2 = 0 := Nat.choose_eq_zero_iff.mpr (by omega)
  have h3 : n.choose 3 = 0 := Nat.choose_eq_zero_iff.mpr (by omega)
  unfold occH
  rw [h2, h3]
  norm_num

/-- The closed form `2 * C(n,2) = n * (n - 1)`, cast to `ℝ` (avoiding the ℕ-division in
`Nat.choose_two_right`). -/
private lemma two_mul_cast_choose_two (n : ℕ) :
    2 * (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  rcases n with _ | j
  · have h2 : (0 : ℕ).choose 2 = 0 := Nat.choose_eq_zero_iff.mpr (by omega)
    norm_num [h2]
  · have hj1 : (j : ℕ).choose 1 = j := Nat.choose_one_right j
    have h : (j + 1) * (j : ℕ).choose 1 = (j + 1).choose 2 * 2 := Nat.add_one_mul_choose_eq j 1
    rw [hj1] at h
    have h' : (((j + 1) * j : ℕ) : ℝ) = (((j + 1).choose 2 * 2 : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    linarith

/-- The increment identity: `occW j` is the difference `occH (j+1) - occH j`. -/
private lemma occW_succ (j : ℕ) : occW (j + 1) = occH (j + 1) - occH j := by
  have h2 : (j + 1).choose 2 = (j : ℕ).choose 1 + j.choose 2 := Nat.choose_succ_succ j 1
  have h3 : (j + 1).choose 3 = j.choose 2 + j.choose 3 := Nat.choose_succ_succ j 2
  have hc1 : ((j : ℕ).choose 1 : ℝ) = (j : ℝ) := by exact_mod_cast Nat.choose_one_right j
  have key := two_mul_cast_choose_two j
  unfold occW occH
  rw [h2, h3]
  push_cast
  rw [hc1]
  linear_combination (1 / 2) * key

theorem occH_eq_sum_occW (n : ℕ) : occH n = ∑ j ∈ Finset.Icc 2 n, occW j := by
  induction n with
  | zero =>
    have hE : Finset.Icc 2 0 = ∅ := Finset.Icc_eq_empty (by omega)
    have h0 : occH 0 = 0 := occH_eq_zero_of_le_one 0 (by omega)
    rw [hE, Finset.sum_empty, h0]
  | succ n ih =>
    rcases n with _ | n'
    · have hE : Finset.Icc 2 1 = ∅ := Finset.Icc_eq_empty (by omega)
      have h0 : occH 1 = 0 := occH_eq_zero_of_le_one 1 (by omega)
      rw [hE, Finset.sum_empty, h0]
    · have hsplit : ∑ j ∈ Finset.Icc 2 (n' + 1 + 1), occW j
          = (∑ j ∈ Finset.Icc 2 (n' + 1), occW j) + occW (n' + 1 + 1) :=
        Finset.sum_Icc_succ_top (a := 2) (b := n' + 1) (f := occW) (by omega)
      rw [hsplit]
      linarith [ih, occW_succ (n' + 1)]

end Work.Deep.Sparse
