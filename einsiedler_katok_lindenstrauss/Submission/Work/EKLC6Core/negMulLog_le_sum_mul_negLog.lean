import Mathlib

/-!
# The Gibbs inequality for `negMulLog` against a sub-probability weight

For a probability vector `σ` (`σ ≥ 0`, `∑ σ = 1`) and a sub-probability vector `τ`
(`τ ≥ 0`, `∑ τ ≤ 1`) whose support contains that of `σ`, the cross entropy dominates the
Shannon entropy:

`∑ i, Real.negMulLog (σ i) ≤ ∑ i, σ i * (- Real.log (τ i))`.

Equivalently, the relative entropy `∑ i, σ i * (log (σ i) - log (τ i))` is nonnegative.
The proof is the classical one: for `x ≥ 0` and `y > 0` (or `x = 0`) one has the pointwise
*Gibbs bound* `x - y ≤ x log x - x log y`, obtained from `log u ≤ u - 1` at `u = x / y`;
summing and using `∑ σ = 1 ≥ ∑ τ` yields the claim.
-/

namespace Work.EKLC6Core

/-- **Pointwise Gibbs bound.** For `x ≥ 0`, `y ≥ 0` with `y > 0` whenever `x > 0`,
`x * log x - x * log y ≥ x - y`. This is the tangent-line (or `log u ≤ u - 1`) estimate
`σ log σ - σ log τ ≥ σ - τ` used in the proof of the Gibbs inequality. -/
lemma mul_log_sub_mul_log_ge (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x = 0 ∨ 0 < y) :
    x - y ≤ x * Real.log x - x * Real.log y := by
  rcases h with h | hypos
  · rw [h]; simp only [mul_zero, sub_zero, zero_mul, Real.log_zero]; linarith
  · rcases eq_or_lt_of_le hx with hx0 | hxpos
    · rw [← hx0]; simp only [mul_zero, sub_zero, zero_mul, Real.log_zero]; linarith
    · have ht : 0 < x / y := div_pos hxpos hypos
      have key := Real.self_sub_one_le_mul_log (le_of_lt ht)
      have hlog : Real.log (x / y) = Real.log x - Real.log y :=
        Real.log_div (ne_of_gt hxpos) (ne_of_gt hypos)
      rw [hlog] at key
      have hmul : y * (x / y - 1) ≤ y * ((x / y) * (Real.log x - Real.log y)) :=
        mul_le_mul_of_nonneg_left key (le_of_lt hypos)
      have h1 : y * (x / y - 1) = x - y := by
        rw [mul_sub, mul_one, mul_div_cancel₀ x (ne_of_gt hypos)]
      have h2 : y * ((x / y) * (Real.log x - Real.log y)) = x * Real.log x - x * Real.log y := by
        rw [← mul_assoc, mul_div_cancel₀ x (ne_of_gt hypos), mul_sub]
      linarith [hmul, h1, h2]

/-- **Gibbs' inequality for `negMulLog`.** For a probability vector `σ` and a sub-probability
weight `τ` supported on the support of `σ`, the entropy `∑ -σ log σ` is at most the cross
entropy `∑ σ (-log τ)`. -/
theorem negMulLog_le_sum_mul_negLog {n : ℕ} (σ τ : Fin n → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hσsum : ∑ i, σ i = 1) (hτ : ∀ i, 0 ≤ τ i) (hτsum : ∑ i, τ i ≤ 1)
    (hστ : ∀ i, σ i ≠ 0 → τ i ≠ 0) :
    ∑ i, Real.negMulLog (σ i) ≤ ∑ i, σ i * (- Real.log (τ i)) := by
  have hptw : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      σ i - τ i ≤ σ i * Real.log (σ i) - σ i * Real.log (τ i) := by
    intro i _
    exact mul_log_sub_mul_log_ge (σ i) (τ i) (hσ i) (hτ i) (by
      rcases eq_or_ne (σ i) 0 with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_le_of_ne (hτ i) (Ne.symm (hστ i h))))
  have hle : ∑ i, (σ i - τ i) ≤
      ∑ i, (σ i * Real.log (σ i) - σ i * Real.log (τ i)) := Finset.sum_le_sum hptw
  have hsum1 : ∑ i, (σ i - τ i) = 1 - ∑ i, τ i := by
    rw [Finset.sum_sub_distrib, hσsum]
  have h0 : (0 : ℝ) ≤ ∑ i, σ i * Real.log (σ i) - ∑ i, σ i * Real.log (τ i) := by
    rw [← Finset.sum_sub_distrib]
    linarith [hle, hsum1, hτsum]
  have hBA : ∑ i, σ i * Real.log (τ i) ≤ ∑ i, σ i * Real.log (σ i) := by linarith
  calc ∑ i, Real.negMulLog (σ i)
      = ∑ i, -(σ i * Real.log (σ i)) := by
          apply Finset.sum_congr rfl; intro i _; rw [Real.negMulLog_eq_neg]
    _ = - ∑ i, σ i * Real.log (σ i) := Finset.sum_neg_distrib _
    _ ≤ - ∑ i, σ i * Real.log (τ i) := neg_le_neg hBA
    _ = ∑ i, -(σ i * Real.log (τ i)) := (Finset.sum_neg_distrib _).symm
    _ = ∑ i, σ i * (- Real.log (τ i)) := by
          apply Finset.sum_congr rfl; intro i _; ring

end Work.EKLC6Core
