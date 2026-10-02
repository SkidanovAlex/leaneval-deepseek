/-
# `occHtrunc J` is `occWsum J`-Lipschitz in the class size

The truncated class contribution `occHtrunc J n = occH (min n J)` of
`Submission/Work/Deep/Sparse/NcpDefs.lean` is a partial sum of the increments
`occW j = occH j - occH (j - 1)`, cut off at `J`.  Consequently

  `|occHtrunc J n - occHtrunc J m| ≤ occWsum J * |n - m|`,

where `occWsum J = ∑_{2 ≤ j ≤ J} |occW j|` is the total variation of the
increment sequence over the retained range.  This is the Lipschitz constant
that makes the slice statistics `occSlice`/`occClass` self-bounding.

The proof is elementary: `occH k` is the sum of `occW j` over `2 ≤ j ≤ k`, so
the difference of two truncations is the sum of `occW` over a *difference* of
two nested interval sums contained in `Icc 2 J`; the absolute value is at most
the sum of the absolute values over that difference, which is at most the full
`occWsum J`.  Since the two arguments differ by a nonzero natural number they
differ by at least `1` as reals, which upgrades the bound to the stated
`occWsum J * |n - m|`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.NcpDefs

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Sparse

/-- `occW` is the increment of `occH`, in a form with the `2` in the numerator:
`2 * C(N,2) = N (N - 1)`. -/
private lemma occHtrunc_two_mul_choose_two (N : ℕ) :
    ((N.choose 2 : ℕ) : ℝ) * 2 = (N : ℝ) * ((N : ℝ) - 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    nlinarith [ih]

/-- The increment identity `occH (j + 1) = occH j + occW (j + 1)`. -/
private lemma occHtrunc_occH_succ (j : ℕ) : occH (j + 1) = occH j + occW (j + 1) := by
  have h2 : ((j + 1).choose 2 : ℝ) = (j : ℝ) + (j.choose 2 : ℝ) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; ring
  have h3 : ((j + 1).choose 3 : ℝ) = (j.choose 2 : ℝ) + (j.choose 3 : ℝ) := by
    rw [Nat.choose_succ_succ]; push_cast; ring
  have hc2 := occHtrunc_two_mul_choose_two j
  simp only [occH, occW, h2, h3]
  push_cast
  nlinarith [hc2]

/-- `occH N` is the sum of the increments `occW j` over `2 ≤ j ≤ N`. -/
private lemma occHtrunc_occH_eq_sum_Icc (N : ℕ) : occH N = ∑ j ∈ Finset.Icc 2 N, occW j := by
  induction N with
  | zero => simp [occH]
  | succ N ih =>
    by_cases h : 1 ≤ N
    · rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1), ← ih]
      exact occHtrunc_occH_succ N
    · interval_cases N
      simp [occH, Nat.choose_eq_zero_iff]

/-- The core Lipschitz bound: two truncation levels `a ≤ b ≤ J` differ by at most
`occWsum J`. -/
private lemma occHtrunc_abs_occH_sub_le (J a b : ℕ) (_ha : a ≤ J) (hb : b ≤ J) (hab : a ≤ b) :
    |occH b - occH a| ≤ occWsum J := by
  rw [occHtrunc_occH_eq_sum_Icc b, occHtrunc_occH_eq_sum_Icc a]
  have hsub : Finset.Icc 2 a ⊆ Finset.Icc 2 b := Finset.Icc_subset_Icc_right hab
  have hsdiff : Finset.Icc 2 b \ Finset.Icc 2 a ⊆ Finset.Icc 2 J :=
    fun x hx => Finset.Icc_subset_Icc_right hb (Finset.mem_sdiff.mp hx).1
  have h1 : (∑ j ∈ Finset.Icc 2 b, occW j) - (∑ j ∈ Finset.Icc 2 a, occW j)
      = ∑ j ∈ Finset.Icc 2 b \ Finset.Icc 2 a, occW j := by
    have hh := Finset.sum_sdiff hsub (f := occW)
    linarith
  rw [h1]
  calc |∑ j ∈ Finset.Icc 2 b \ Finset.Icc 2 a, occW j|
      ≤ ∑ j ∈ Finset.Icc 2 b \ Finset.Icc 2 a, |occW j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 2 J, |occW j| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsdiff (fun i _ _ => abs_nonneg _)
    _ = occWsum J := rfl

/-- Distinct natural numbers differ by at least `1` as reals. -/
private lemma occHtrunc_one_le_abs_cast_sub (n m : ℕ) (h : n ≠ m) :
    (1 : ℝ) ≤ |(n : ℝ) - (m : ℝ)| := by
  rcases lt_or_gt_of_ne h with h | h
  · have hm : ((m - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := Nat.cast_sub h.le
    have hge : (1 : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
      have : 1 ≤ m - n := by omega
      exact_mod_cast this
    have hnonneg : 0 ≤ (m : ℝ) - (n : ℝ) := hm ▸ Nat.cast_nonneg _
    calc (1 : ℝ) ≤ ((m - n : ℕ) : ℝ) := hge
      _ = (m : ℝ) - (n : ℝ) := hm
      _ = |(m : ℝ) - (n : ℝ)| := (abs_of_nonneg hnonneg).symm
      _ = |(n : ℝ) - (m : ℝ)| := abs_sub_comm _ _
  · have hn : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := Nat.cast_sub h.le
    have hge : (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
      have : 1 ≤ n - m := by omega
      exact_mod_cast this
    have hnonneg : 0 ≤ (n : ℝ) - (m : ℝ) := hn ▸ Nat.cast_nonneg _
    calc (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := hge
      _ = (n : ℝ) - (m : ℝ) := hn
      _ = |(n : ℝ) - (m : ℝ)| := (abs_of_nonneg hnonneg).symm

theorem occHtrunc_sub_le (J n m : ℕ) :
    |occHtrunc J n - occHtrunc J m| ≤ occWsum J * |(n : ℝ) - (m : ℝ)| := by
  rcases eq_or_ne n m with rfl | hne
  · simp
  · -- On a nonzero difference the factor `|n - m|` is at least `1`,
    -- so it suffices to bound the left side by `occWsum J`.
    have hcore : |occHtrunc J n - occHtrunc J m| ≤ occWsum J := by
      rcases le_total (min n J) (min m J) with h | h
      · have hh := occHtrunc_abs_occH_sub_le J (min n J) (min m J)
          (min_le_right _ _) (min_le_right _ _) h
        simp only [occHtrunc]
        rw [abs_sub_comm]
        exact hh
      · have hh := occHtrunc_abs_occH_sub_le J (min m J) (min n J)
          (min_le_right _ _) (min_le_right _ _) h
        simpa only [occHtrunc] using hh
    have h1 := occHtrunc_one_le_abs_cast_sub n m hne
    calc |occHtrunc J n - occHtrunc J m| ≤ occWsum J := hcore
      _ = occWsum J * 1 := (mul_one _).symm
      _ ≤ occWsum J * |(n : ℝ) - (m : ℝ)| :=
          mul_le_mul_of_nonneg_left h1 (Finset.sum_nonneg fun j _ => abs_nonneg _)

end Work.Deep.Sparse
