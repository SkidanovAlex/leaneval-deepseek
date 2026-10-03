import Mathlib
import Submission.Work.L62.exp_neg_two_mul_le_one_sub
import Submission.Work.L62.prod_range_bounds

/-!
# The tail product bound (Shishikura, §6)

Let `a : ℕ → ℂ` be a sequence with `‖a k - 1‖ ≤ c * μ ^ k`, where `0 ≤ c ≤ 1/2` and
`0 ≤ μ < 1`.  Then the partial products `∏_{k < m} a k` stay within a factor
`exp (c / (1 - μ))` of `1`, in both directions, and their distance from `1` is at most
`exp (c / (1 - μ)) - 1`.

The two ingredients are:
* `Work.L62.prod_range_bounds` — the elementary product estimates
  `‖∏ (a k) - 1‖ ≤ ∏ (1 + b k) - 1`, `∏ (1 - b k) ≤ ‖∏ a k‖ ≤ ∏ (1 + b k)`
  for any majorant `b k ≥ ‖a k - 1‖` with `b k ≤ 1/2`;
* `Work.L62.exp_neg_two_mul_le_one_sub` — the pointwise bound `exp (-2t) ≤ 1 - t` for
  `0 ≤ t ≤ 1/2`, which turns the lower product bound into an exponential.

Both products are then compared with `exp` using `1 + x ≤ exp x` and the elementary bound
`∑_{k < m} c μ^k ≤ c / (1 - μ)`.
-/

namespace Work.L62

theorem tail_prod_bound {a : ℕ → ℂ} {c μ : ℝ} (hc0 : 0 ≤ c) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hc : c ≤ 1 / 2) (ha : ∀ k : ℕ, ‖a k - 1‖ ≤ c * μ ^ k) (m : ℕ) :
    ‖(∏ k ∈ Finset.range m, a k) - 1‖ ≤ Real.exp (c / (1 - μ)) - 1 ∧
    Real.exp (-(2 * (c / (1 - μ)))) ≤ ‖(∏ k ∈ Finset.range m, a k)‖ ∧
    ‖(∏ k ∈ Finset.range m, a k)‖ ≤ Real.exp (c / (1 - μ)) := by
  have hμ1' : (0 : ℝ) < 1 - μ := by linarith
  set b : ℕ → ℝ := fun k => c * μ ^ k with hb_def
  have hb0 : ∀ k, 0 ≤ b k := fun k => mul_nonneg hc0 (pow_nonneg hμ0 k)
  have hble : ∀ k, b k ≤ 1 / 2 := fun k => by
    have hpow : μ ^ k ≤ 1 := pow_le_one₀ hμ0 (le_of_lt hμ1)
    calc b k = c * μ ^ k := rfl
      _ ≤ (1 / 2) * 1 := mul_le_mul hc hpow (pow_nonneg hμ0 k) (by norm_num)
      _ = 1 / 2 := by norm_num
  have hbnd := prod_range_bounds (a := a) (b := b) hb0 hble (by simpa [hb_def] using ha) m
  obtain ⟨h1, h2, h3⟩ := hbnd
  -- geometric-series bound `∑_{k<m} μ^k ≤ 1/(1-μ)`
  have hgeom : (∑ k ∈ Finset.range m, μ ^ k) * (1 - μ) = 1 - μ ^ m := by
    have h := geom_sum_mul μ m
    linear_combination -h
  have hsum_le : ∑ k ∈ Finset.range m, b k ≤ c / (1 - μ) := by
    have hsumμ : ∑ k ∈ Finset.range m, μ ^ k ≤ 1 / (1 - μ) := by
      rw [le_div_iff₀ hμ1']
      nlinarith [hgeom, pow_nonneg hμ0 m]
    calc ∑ k ∈ Finset.range m, b k = c * ∑ k ∈ Finset.range m, μ ^ k := by
          simp [hb_def, Finset.mul_sum]
      _ ≤ c * (1 / (1 - μ)) := mul_le_mul_of_nonneg_left hsumμ hc0
      _ = c / (1 - μ) := by ring
  -- upper bounds: `∏ (1 + b k) ≤ exp (c/(1-μ))`
  have hP : (∏ k ∈ Finset.range m, (1 + b k)) ≤ Real.exp (c / (1 - μ)) := by
    calc (∏ k ∈ Finset.range m, (1 + b k)) ≤ ∏ k ∈ Finset.range m, Real.exp (b k) :=
          Finset.prod_le_prod₀ (fun k _ => by linarith [hb0 k])
            (fun k _ => by linarith [Real.add_one_le_exp (b k)])
      _ = Real.exp (∑ k ∈ Finset.range m, b k) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (c / (1 - μ)) := Real.exp_le_exp.mpr hsum_le
  -- lower bound: `exp (-2 c/(1-μ)) ≤ ∏ (1 - b k)`
  have hQ : Real.exp (-(2 * (c / (1 - μ)))) ≤ (∏ k ∈ Finset.range m, (1 - b k)) := by
    have hsum2 : ∑ k ∈ Finset.range m, (-(2 * b k)) = -(2 * ∑ k ∈ Finset.range m, b k) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      rw [Finset.mul_sum]
    calc Real.exp (-(2 * (c / (1 - μ)))) ≤ Real.exp (-(2 * ∑ k ∈ Finset.range m, b k)) :=
          Real.exp_le_exp.mpr (by linarith [hsum_le])
      _ = Real.exp (∑ k ∈ Finset.range m, (-(2 * b k))) := by rw [hsum2]
      _ = ∏ k ∈ Finset.range m, Real.exp (-(2 * b k)) := Real.exp_sum _ _
      _ ≤ ∏ k ∈ Finset.range m, (1 - b k) :=
          Finset.prod_le_prod₀ (fun k _ => Real.exp_nonneg _)
            (fun k _ => exp_neg_two_mul_le_one_sub (hb0 k) (hble k))
  exact ⟨le_trans h1 (by linarith [hP]), le_trans hQ h2, le_trans h3 hP⟩

end Work.L62
