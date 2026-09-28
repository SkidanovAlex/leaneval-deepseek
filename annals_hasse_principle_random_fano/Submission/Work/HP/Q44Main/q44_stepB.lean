import Mathlib

/-!
# `Work.HP.Q44Main.q44_stepB`

Bound for the triple sum
`∑_{a,b,c ≤ N} [a + b + c ≤ N] · (1/4)^{a+b} ≤ 2 (N + 1)`.

The proof only uses two elementary estimates.

* For fixed `a b`, at most `N + 1` values of `c` contribute and each contributes at most
  `(1/4)^{a+b}`, so the inner `c`-sum is at most `(N+1) · (1/4)^{a+b}`.
* Hence the whole sum is at most `(N+1) · ∑_{a,b ≤ N} (1/4)^{a+b}
  = (N+1) · (∑_{a ≤ N} (1/4)^a)²`, and each factor is a truncated geometric series,
  bounded by `4/3`.  Thus the sum is at most `(N+1) · 16/9 ≤ 2 (N+1)`.
-/

namespace Work.HP.Q44Main

/-- Truncated geometric series with ratio `1/4`: `∑_{i<n} (1/4)^i ≤ 4/3`. -/
private lemma q44_stepB_geom (n : ℕ) :
    (∑ i ∈ Finset.range n, ((1 : ℝ) / 4) ^ i) ≤ 4 / 3 := by
  rw [geom_sum_eq (by norm_num : ((1 : ℝ) / 4) ≠ 1)]
  have hxn : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ n := by positivity
  have hx1 : ((1 : ℝ) / 4) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hkey : (((1 : ℝ) / 4) ^ n - 1) / ((1 : ℝ) / 4 - 1)
      = (4 / 3) * (1 - ((1 : ℝ) / 4) ^ n) := by
    rw [div_eq_iff (by norm_num : ((1 : ℝ) / 4 - 1) ≠ 0)]
    ring
  rw [hkey]
  nlinarith [hxn, hx1]

theorem q44_stepB (N : ℕ) :
    (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
      (if a + b + c ≤ N then ((1 : ℝ) / 4) ^ (a + b) else 0))
    ≤ 2 * ((N : ℝ) + 1) := by
  -- Inner `c`-sum: at most `N+1` non-zero-or-negative terms, each `≤ (1/4)^{a+b}`.
  have hinner : ∀ a b : ℕ,
      (∑ c ∈ Finset.range (N + 1), (if a + b + c ≤ N then ((1 : ℝ) / 4) ^ (a + b) else 0))
        ≤ ((N : ℝ) + 1) * ((1 : ℝ) / 4) ^ (a + b) := by
    intro a b
    have hnn : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ (a + b) := by positivity
    calc (∑ c ∈ Finset.range (N + 1), (if a + b + c ≤ N then ((1 : ℝ) / 4) ^ (a + b) else 0))
        ≤ ∑ c ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ (a + b) := by
          apply Finset.sum_le_sum
          intro c _
          by_cases h : a + b + c ≤ N
          · rw [ite_eq_left h]
          · rw [ite_eq_right h]; exact hnn
      _ = ((N : ℝ) + 1) * ((1 : ℝ) / 4) ^ (a + b) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- Factoring the double sum into a product of two geometric sums.
  have hfac :
      (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
        ((N : ℝ) + 1) * (((1 : ℝ) / 4) ^ a * ((1 : ℝ) / 4) ^ b))
      = ((N : ℝ) + 1) *
        ((∑ a ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ a) *
         (∑ b ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ b)) := by
    have h1 : (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
          ((N : ℝ) + 1) * (((1 : ℝ) / 4) ^ a * ((1 : ℝ) / 4) ^ b))
        = ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
          (((N : ℝ) + 1) * ((1 : ℝ) / 4) ^ a) * ((1 : ℝ) / 4) ^ b := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      ring
    have h2 : (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
          (((N : ℝ) + 1) * ((1 : ℝ) / 4) ^ a) * ((1 : ℝ) / 4) ^ b)
        = (∑ a ∈ Finset.range (N + 1), ((N : ℝ) + 1) * ((1 : ℝ) / 4) ^ a) *
          (∑ b ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ b) :=
      (Finset.sum_mul_sum _ _ (fun a => ((N : ℝ) + 1) * ((1 : ℝ) / 4) ^ a)
        (fun b => ((1 : ℝ) / 4) ^ b)).symm
    have h3 : (∑ a ∈ Finset.range (N + 1), ((N : ℝ) + 1) * ((1 : ℝ) / 4) ^ a)
        = ((N : ℝ) + 1) * (∑ a ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ a) :=
      (Finset.mul_sum _ (fun a => ((1 : ℝ) / 4) ^ a) ((N : ℝ) + 1)).symm
    rw [h1, h2, h3, mul_assoc]
  calc (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
        (if a + b + c ≤ N then ((1 : ℝ) / 4) ^ (a + b) else 0))
      ≤ ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
          ((N : ℝ) + 1) * ((1 : ℝ) / 4) ^ (a + b) := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro b _
        exact hinner a b
    _ = ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
          ((N : ℝ) + 1) * (((1 : ℝ) / 4) ^ a * ((1 : ℝ) / 4) ^ b) := by
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        rw [pow_add]
    _ = ((N : ℝ) + 1) *
        ((∑ a ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ a) *
         (∑ b ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ b)) := hfac
    _ ≤ ((N : ℝ) + 1) * (4 / 3 * (4 / 3)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul (q44_stepB_geom (N + 1)) (q44_stepB_geom (N + 1))
            (Finset.sum_nonneg (fun i _ => by positivity)) (by norm_num)
        · positivity
    _ ≤ 2 * ((N : ℝ) + 1) := by
        have : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
        nlinarith

end Work.HP.Q44Main
