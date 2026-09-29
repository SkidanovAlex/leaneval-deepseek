import Mathlib

/-!
# Elementary estimates around Euler's pentagonal number theorem for `ℂ`

These are the small estimates used to discharge the summability, multipliability and
convergence hypotheses of `Pentagonal.tprod_one_sub_pow` (Mathlib's pentagonal number theorem)
at a complex number `q` with `‖q‖ < 1`.

* `sum_pow_range_le`: uniform geometric bound `∑_{i=0}^{n} r^{k+i+1} ≤ r/(1-r)`;
* `norm_prod_range_one_sub_pow_le`: the partial products `∏_{i=0}^{n}(1 - q^{k+i+1})` are
  uniformly bounded by `exp (‖q‖/(1-‖q‖))`;
* `le_pentagonal_neg`, `le_pentagonal_add_one`: the generalized pentagonal numbers grow at least
  linearly: `k ≤ pentagonal (-k)` and `k + 1 ≤ pentagonal (k+1)`.
-/

open scoped BigOperators

namespace Work.Haupt

/-- For `0 ≤ r < 1` the finite geometric sum `∑_{i=0}^{n} r^{k+i+1}` is at most `r/(1-r)`,
uniformly in `k` and `n`. -/
theorem sum_pow_range_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), r ^ (k + i + 1) ≤ r / (1 - r) := by
  have hgs : Summable (fun j : ℕ => r ^ (j + 1)) := by
    rw [summable_nat_add_iff 1]
    exact summable_geometric_of_lt_one hr0 hr1
  have htsum : ∑' j : ℕ, r ^ (j + 1) = r / (1 - r) := by
    have h1 : ∑' j : ℕ, r ^ (j + 1) = ∑' j : ℕ, r * r ^ j := by
      apply tsum_congr; intro j; rw [pow_succ]; ring
    rw [h1, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  calc ∑ i ∈ Finset.range (n + 1), r ^ (k + i + 1)
      ≤ ∑ i ∈ Finset.range (n + 1), r ^ (i + 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
    _ ≤ ∑' j : ℕ, r ^ (j + 1) := hgs.sum_le_tsum _ (fun i _ => by positivity)
    _ = r / (1 - r) := htsum

/-- The partial products `∏_{i=0}^{n}(1 - q^{k+i+1})` are uniformly bounded by
`exp (‖q‖/(1-‖q‖))` in `k` and `n`. -/
theorem norm_prod_range_one_sub_pow_le {q : ℂ} (hq : ‖q‖ < 1) (k n : ℕ) :
    ‖∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖ ≤ Real.exp (‖q‖ / (1 - ‖q‖)) := by
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg q
  calc ‖∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))‖
      ≤ ∏ i ∈ Finset.range (n + 1), ‖1 - q ^ (k + i + 1)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ i ∈ Finset.range (n + 1), (1 + ‖q‖ ^ (k + i + 1)) := by
        apply Finset.prod_le_prod₀
        · intro i _; positivity
        · intro i _
          calc ‖1 - q ^ (k + i + 1)‖ ≤ ‖(1 : ℂ)‖ + ‖q ^ (k + i + 1)‖ := norm_sub_le _ _
            _ = 1 + ‖q‖ ^ (k + i + 1) := by rw [norm_one, norm_pow]
    _ ≤ Real.exp (∑ i ∈ Finset.range (n + 1), ‖q‖ ^ (k + i + 1)) :=
        Real.prod_one_add_le_exp_sum _ (fun i => by positivity)
    _ ≤ Real.exp (‖q‖ / (1 - ‖q‖)) :=
        Real.exp_le_exp.mpr (sum_pow_range_le hr0 hq k n)

/-- `k ≤ pentagonal (-k)`. -/
theorem le_pentagonal_neg (k : ℕ) : k ≤ pentagonal (-(k : ℤ)) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0; simp [pentagonal_def]
  · have h2 := two_mul_natCast_pentagonal_neg (k : ℤ)
    have hnat : 2 * k ≤ k * (3 * k + 1) := by
      rw [mul_comm 2 k]
      exact Nat.mul_le_mul_left k (by omega)
    have hk : (k : ℤ) ≤ ((pentagonal (-(k : ℤ))) : ℤ) := by
      have h3 : (2 : ℤ) * ((k : ℕ) : ℤ) ≤ 2 * ((pentagonal (-(k : ℤ))) : ℤ) := by
        rw [h2]; exact_mod_cast hnat
      linarith
    exact Nat.cast_le.mp hk

/-- `k + 1 ≤ pentagonal (k+1)`. -/
theorem le_pentagonal_add_one (k : ℕ) : k + 1 ≤ pentagonal ((k : ℤ) + 1) := by
  have h2 := two_mul_natCast_pentagonal ((k : ℤ) + 1)
  have h2' : 2 * ((pentagonal ((k : ℤ) + 1)) : ℤ) = (((k + 1) * (3 * k + 2) : ℕ) : ℤ) := by
    rw [h2]; push_cast; ring
  have hnat : 2 * (k + 1) ≤ (k + 1) * (3 * k + 2) := by
    rw [mul_comm 2 (k + 1)]
    exact Nat.mul_le_mul_left (k + 1) (by omega)
  have hk : (((k + 1 : ℕ)) : ℤ) ≤ ((pentagonal ((k : ℤ) + 1)) : ℤ) := by
    have h3 : (2 : ℤ) * (((k + 1 : ℕ)) : ℤ)
        ≤ 2 * ((pentagonal ((k : ℤ) + 1)) : ℤ) := by
      rw [h2']; exact_mod_cast hnat
    linarith
  exact Nat.cast_le.mp hk

end Work.Haupt
