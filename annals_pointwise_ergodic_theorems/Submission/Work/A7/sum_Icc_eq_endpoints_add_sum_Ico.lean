import Mathlib

namespace Work.A7

/-!
# The trapezoidal (endpoint) identity for sums over an integer interval

For an integer interval `[a, b]` (`a ≤ b`) and any `w : ℝ → ℂ`, the sum of `w` over the
integer points of `[a, b]` is the average of the two endpoint values plus the sum over the
unit sub-intervals `[n, n+1]` (`a ≤ n < b`) of the average of `w` at their endpoints:

`∑_{n ∈ Icc a b} w n = (w a + w b)/2 + ∑_{n ∈ Ico a b} (w n + w (n+1))/2`.

This is the exact algebraic identity underlying the trapezoidal approximation of an integral
by a sum: each interior point `a < n < b` is counted once on the left and twice (once as the
right endpoint of `[n-1, n]`, once as the left endpoint of `[n, n+1]`) with weight `1/2` on the
right, while each of the two endpoints is counted once on the left and once with weight `1/2`
on the right.
-/

/-- The endpoint identity in the "pure `ℤ`-indexed" form, for an arbitrary sequence
`g : ℤ → ℂ`.  The displayed theorem below is the case `g n = w (n : ℝ)`. -/
private lemma sum_Icc_eq_endpoints_add_sum_Ico_int (g : ℤ → ℂ) {a b : ℤ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b, g n) = (g a + g b) / 2 + ∑ n ∈ Finset.Ico a b, (g n + g (n + 1)) / 2 := by
  -- Split the `Ico` sum against the two shifted full ranges `[a, b-1]` and `[a+1, b]`.
  have hLeft : (∑ n ∈ Finset.Ico a b, g n) = ∑ n ∈ Finset.Icc a (b - 1), g n := by
    rw [← Finset.Icc_sub_one_right_eq_Ico (a := a) (b := b)]
  have hShift : (∑ n ∈ Finset.Ico a b, g (n + 1)) = ∑ n ∈ Finset.Icc (a + 1) b, g n := by
    have h1 : (∑ n ∈ Finset.Ico a b, g (n + 1)) = ∑ n ∈ Finset.Ico a b, g (1 + n) := by
      simp [add_comm]
    rw [h1, Finset.sum_Ico_add]
    rw [Finset.Ico_add_one_right_eq_Icc]
  -- Peel off the two endpoints of `[a, b]`.
  have hRight : (∑ n ∈ Finset.Icc a b, g n) = g a + ∑ n ∈ Finset.Icc (a + 1) b, g n := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hab, Finset.sum_insert (by simp)]
  have hLeftTop : (∑ n ∈ Finset.Icc a b, g n) = (∑ n ∈ Finset.Icc a (b - 1), g n) + g b := by
    rw [← Finset.insert_Icc_sub_one_right_eq_Icc hab, Finset.sum_insert (by simp)]
    rw [add_comm]
  have hSum : (∑ n ∈ Finset.Ico a b, (g n + g (n + 1)))
      = (∑ n ∈ Finset.Icc a (b - 1), g n) + ∑ n ∈ Finset.Icc (a + 1) b, g n := by
    rw [Finset.sum_add_distrib, hLeft, hShift]
  -- Twice the left-hand side equals the sum of the two "peeled" expressions.
  have hKey : 2 * (∑ n ∈ Finset.Icc a b, g n)
      = (g a + g b) + ∑ n ∈ Finset.Ico a b, (g n + g (n + 1)) := by
    rw [hSum]
    calc 2 * (∑ n ∈ Finset.Icc a b, g n)
        = (∑ n ∈ Finset.Icc a b, g n) + (∑ n ∈ Finset.Icc a b, g n) := by rw [two_mul]
      _ = (g a + ∑ n ∈ Finset.Icc (a + 1) b, g n) + (∑ n ∈ Finset.Icc a b, g n) := by
            rw [hRight]
      _ = (g a + ∑ n ∈ Finset.Icc (a + 1) b, g n)
            + ((∑ n ∈ Finset.Icc a (b - 1), g n) + g b) := by rw [hLeftTop]
      _ = (g a + g b) + ((∑ n ∈ Finset.Icc a (b - 1), g n)
            + ∑ n ∈ Finset.Icc (a + 1) b, g n) := by ring
  have hS : (∑ n ∈ Finset.Icc a b, g n)
      = ((g a + g b) + ∑ n ∈ Finset.Ico a b, (g n + g (n + 1))) / 2 := by
    rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0), mul_comm]
    exact hKey
  rw [hS, ← Finset.sum_div, hSum]
  ring

theorem sum_Icc_eq_endpoints_add_sum_Ico (w : ℝ → ℂ) {a b : ℤ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b, w (n : ℝ))
      = (w (a : ℝ) + w (b : ℝ)) / 2
        + ∑ n ∈ Finset.Ico a b, (w (n : ℝ) + w ((n : ℝ) + 1)) / 2 := by
  simpa only [Int.cast_add, Int.cast_one] using
    (sum_Icc_eq_endpoints_add_sum_Ico_int (fun n : ℤ => w (n : ℝ)) hab)

end Work.A7
