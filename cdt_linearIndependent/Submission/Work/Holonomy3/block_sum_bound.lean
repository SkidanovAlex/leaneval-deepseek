import Mathlib
import Submission.Work.Holonomy3.threshold_sum_eval
import Submission.Work.Holonomy3.ceil_sq_error

namespace Work.Holonomy3

/-!
# The discrete block sum

We prove `block_sum_bound`: for `0 ≤ a ≤ b ≤ 1` and `d ≥ 1`, the sum of the grid points
`j/d ∈ [a,b)` over `j : Fin d` agrees with `(d/2)·(b²-a²)` up to an absolute error of at most `5`.

The proof has three parts.

* **Splitting.** Since `[a ≤ x < b] = [x < b] - [x < a]` on the reals, the block sum splits into the
  difference of the two "threshold sums" `Σ_{j/d < t} j/d`.

* **Exact threshold evaluation** (delegated, `threshold_sum_eval`). For `0 ≤ t ≤ 1`, the indices
  `j : Fin d` with `j/d < t` are exactly `0, …, K-1` with `K = ⌈t·d⌉` (the constraint `j < d` is
  automatic because `t ≤ 1`), so the sum of the `j` equals `K(K-1)/2`.

* **Error bound** (delegated, `ceil_sq_error`). Writing `x = a·d`, `y = b·d` (`0 ≤ x ≤ y ≤ d`), the
  two ceiling errors `⌈x⌉ - x`, `⌈y⌉ - y ∈ [0,1)` give
  `|⌈y⌉(⌈y⌉-1) - ⌈x⌉(⌈x⌉-1) - (y²-x²)| ≤ 5d+2`, and division by `2d ≥ 2` yields an error `≤ 5`.
-/

/-- **The splitting step.** On the reals `[a ≤ x < b] = [x < b] - [x < a]`, hence the block sum is
the difference of the two threshold sums. -/
private lemma block_sum_aux {d : ℕ} (hd : 0 < d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin d =>
          a ≤ (j : ℝ) / (d : ℝ) ∧ (j : ℝ) / (d : ℝ) < b), (j : ℝ) / (d : ℝ))
      = ((Nat.ceil (b * (d : ℝ)) : ℝ) * ((Nat.ceil (b * (d : ℝ)) : ℝ) - 1)
          - (Nat.ceil (a * (d : ℝ)) : ℝ) * ((Nat.ceil (a * (d : ℝ)) : ℝ) - 1))
        / (2 * (d : ℝ)) := by
  -- split the block sum into the difference of the two threshold sums
  have stepB : (∑ j ∈ Finset.univ.filter (fun j : Fin d =>
        a ≤ (j : ℝ) / (d : ℝ) ∧ (j : ℝ) / (d : ℝ) < b), (j : ℝ) / (d : ℝ))
      = (∑ j ∈ Finset.univ.filter (fun j : Fin d => (j : ℝ) / (d : ℝ) < b), (j : ℝ) / (d : ℝ))
        - (∑ j ∈ Finset.univ.filter (fun j : Fin d => (j : ℝ) / (d : ℝ) < a),
            (j : ℝ) / (d : ℝ)) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h1 : (j : ℝ) / (d : ℝ) < a
    · have h1' : ¬ (a ≤ (j : ℝ) / (d : ℝ)) := not_le.mpr h1
      have h2 : (j : ℝ) / (d : ℝ) < b := lt_of_lt_of_le h1 hab
      simp [h1, h1', h2]
    · have ha' : a ≤ (j : ℝ) / (d : ℝ) := le_of_not_gt h1
      by_cases h2 : (j : ℝ) / (d : ℝ) < b
      · simp [h1, ha', h2]
      · simp [h1, ha', h2]
  -- exact evaluation of the two threshold sums
  have hsum_b : (∑ j ∈ Finset.univ.filter (fun j : Fin d => (j : ℝ) / (d : ℝ) < b),
        (j : ℝ) / (d : ℝ))
      = (Nat.ceil (b * (d : ℝ)) : ℝ) * ((Nat.ceil (b * (d : ℝ)) : ℝ) - 1) / (2 * (d : ℝ)) := by
    rw [← Finset.sum_div, threshold_sum_eval d hd (le_trans ha hab) hb, div_div]
  have hsum_a : (∑ j ∈ Finset.univ.filter (fun j : Fin d => (j : ℝ) / (d : ℝ) < a),
        (j : ℝ) / (d : ℝ))
      = (Nat.ceil (a * (d : ℝ)) : ℝ) * ((Nat.ceil (a * (d : ℝ)) : ℝ) - 1) / (2 * (d : ℝ)) := by
    rw [← Finset.sum_div, threshold_sum_eval d hd ha (le_trans hab hb), div_div]
  rw [stepB, hsum_b, hsum_a]
  ring

/-- **The discrete block sum.**  For `0 ≤ a ≤ b ≤ 1` and `d ≥ 1`, the sum of `j/d` over the indices
`j : Fin d` with `j/d ∈ [a,b)` equals `(d/2)·(b²-a²)` up to an error of at most `5`. -/
theorem block_sum_bound {d : ℕ} (hd : 0 < d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(∑ j ∈ Finset.univ.filter (fun j : Fin d =>
          a ≤ (j : ℝ) / (d : ℝ) ∧ (j : ℝ) / (d : ℝ) < b), (j : ℝ) / (d : ℝ))
      - (d : ℝ) / 2 * (b ^ 2 - a ^ 2)| ≤ 5 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
  -- the exact value of the block sum, in terms of the two ceilings
  have h := block_sum_aux hd ha hab hb
  -- the ceiling error estimate with `x = a·d`, `y = b·d`
  have hβ := ceil_sq_error (d := d) (x := a * (d : ℝ)) (y := b * (d : ℝ))
      (mul_nonneg ha (le_of_lt hdR))
      (mul_le_mul_of_nonneg_right hab (le_of_lt hdR))
      (by nlinarith [hb, hdR])
  rw [h]
  -- rewrite the target as a single fraction with denominator `2d`
  have hT : (d : ℝ) / 2 * (b ^ 2 - a ^ 2) = ((b * (d : ℝ)) ^ 2 - (a * (d : ℝ)) ^ 2)
      / (2 * (d : ℝ)) := by
    rw [eq_div_iff (by positivity : (2 * (d : ℝ)) ≠ 0)]
    ring
  rw [hT, ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (d : ℝ))]
  refine le_trans (div_le_div_of_nonneg_right hβ (by positivity)) ?_
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))]
  nlinarith [hd1]

end Work.Holonomy3
