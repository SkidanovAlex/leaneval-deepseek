import Mathlib

set_option linter.unusedVariables false

namespace Work.Pert.LCH

/-- **Pointwise layer-cake bound.**  For `0 ≤ d` and `H > 0`, the reciprocal `1 / max d H` is
dominated by the layer-cake sum over the levels `(i+1)H`: the `i`-th shell contributes its
weight `1/((i+1)H) - 1/((i+2)H)` exactly when the level `(i+2)H` is still at least `d`, and the
tail term `1/((N+1)H)` closes the telescoping.

Proof by induction on `N`.  For `N = 0` the claim is `1/max d H ≤ 1/H`.  In the induction step
the `N`-th summand is `1/((N+1)H) - 1/((N+2)H)` when its indicator is `1`, so the `N+1`-fold
sum is obtained from the `N`-fold sum by replacing the tail `1/((N+1)H)` with `1/((N+2)H)`, which
is exactly the telescoping identity; when the indicator vanishes we have `(N+2)H < d ≤ max d H`
and the tail `1/((N+2)H)` alone already dominates `1/max d H`. -/
theorem layer_cake_pointwise {d H : ℝ} (hd : 0 ≤ d) (hH : 0 < H) (N : ℕ) :
    1 / max d H ≤
      (∑ i ∈ Finset.range N,
        (1 / (((i : ℝ) + 1) * H) - 1 / (((i : ℝ) + 2) * H)) *
          (if d ≤ ((i : ℝ) + 2) * H then (1 : ℝ) else 0))
        + 1 / (((N : ℝ) + 1) * H) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.cast_zero]
    simpa using one_div_le_one_div_of_le hH (le_max_right d H)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hcast : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 2) := by push_cast; ring
    rw [hcast]
    by_cases h : d ≤ ((n : ℝ) + 2) * H
    · rw [ite_eq_left h]
      have hkey : (1 / (((n : ℝ) + 1) * H) - 1 / (((n : ℝ) + 2) * H)) * (1 : ℝ)
          + 1 / (((n : ℝ) + 2) * H) = 1 / (((n : ℝ) + 1) * H) := by
        rw [mul_one, sub_add_cancel]
      linarith [ih, hkey]
    · rw [ite_eq_right h, mul_zero, add_zero]
      have hlt : ((n : ℝ) + 2) * H < d := not_le.mp h
      have hpos : 0 < ((n : ℝ) + 2) * H := by positivity
      have hle : ((n : ℝ) + 2) * H ≤ max d H := le_trans (le_of_lt hlt) (le_max_left d H)
      have hmain : 1 / max d H ≤ 1 / (((n : ℝ) + 2) * H) :=
        one_div_le_one_div_of_le hpos hle
      have hsum : 0 ≤ ∑ i ∈ Finset.range n,
          (1 / (((i : ℝ) + 1) * H) - 1 / (((i : ℝ) + 2) * H)) *
            (if d ≤ ((i : ℝ) + 2) * H then (1 : ℝ) else 0) := by
        apply Finset.sum_nonneg
        intro i _
        apply mul_nonneg _ _
        · have h1 : 0 < ((i : ℝ) + 1) * H := by positivity
          have h2 : ((i : ℝ) + 1) * H ≤ ((i : ℝ) + 2) * H := by nlinarith [hH]
          have := one_div_le_one_div_of_le h1 h2
          linarith
        · split_ifs <;> norm_num
      linarith [hmain, hsum]

end Work.Pert.LCH
