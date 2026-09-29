import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17I.summable_of_rate_bound

/-!
# Shifting power-series sums (`Work.C17I.tsum_shift_lemmas`)

Two elementary, but repeatedly used, manipulations of the value at `w` of a power series:

* `tq j W` is the `j`-fold truncated shift `∑ₙ c_{n+j} Xⁿ` of `W = ∑ₙ cₙ Xⁿ`; therefore
  `w ^ j * (∑' k, coeff k (tq j W) * w ^ k) = (∑' k, coeff k W * w ^ k) - ∑_{m < j} coeff m W * w ^ m`,
  i.e. the tail of the series after the first `j` terms.
* `X * W` is the shift of `W` by one, so evaluates to `w` times the value of `W`.

Both are proved for arbitrary coefficient functions `c : ℕ → ℂ` and summed with the shift
lemmas for `tsum` (`hasSum_nat_add_iff`); the summability input is the workspace lemma
`Work.C17I.summable_of_rate_bound`.
-/

namespace Work.C17I

open scoped BigOperators

/-- Tail of the power series `∑ c k * w ^ k`: the `j`-th tail equals `w ^ j` times the value of
the coefficient sequence shifted by `j`. -/
lemma tsum_shift_mul (c : ℕ → ℂ) {w : ℂ} (h : Summable (fun k => c k * w ^ k)) (j : ℕ) :
    w ^ j * (∑' k : ℕ, c (k + j) * w ^ k)
      = (∑' k : ℕ, c k * w ^ k) - ∑ m ∈ Finset.range j, c m * w ^ m := by
  have h1 : HasSum (fun n : ℕ => c (n + j) * w ^ (n + j))
      ((∑' k : ℕ, c k * w ^ k) - ∑ m ∈ Finset.range j, c m * w ^ m) := by
    have hf : HasSum (fun k : ℕ => c k * w ^ k)
        (((∑' k : ℕ, c k * w ^ k) - ∑ m ∈ Finset.range j, c m * w ^ m)
          + ∑ m ∈ Finset.range j, c m * w ^ m) := by
      rw [sub_add_cancel]
      exact h.hasSum
    exact (hasSum_nat_add_iff j (f := fun k : ℕ => c k * w ^ k)).mpr hf
  have h2 : (∑' n : ℕ, c (n + j) * w ^ (n + j))
      = (∑' n : ℕ, c (n + j) * w ^ n) * w ^ j := by
    rw [← tsum_mul_right]
    exact tsum_congr fun n => by rw [pow_add, mul_assoc]
  calc w ^ j * (∑' k : ℕ, c (k + j) * w ^ k)
      = (∑' k : ℕ, c (k + j) * w ^ k) * w ^ j := by rw [mul_comm]
    _ = ∑' k : ℕ, c (k + j) * w ^ (k + j) := by rw [← h2]
    _ = _ := h1.tsum_eq

/-- For a sequence `g` which is the coefficient sequence of `X * W` (so `g 0 = 0` and
`g (n+1) = c n`), the sum `∑ g k * w ^ k` is `w` times `∑ c k * w ^ k`. -/
lemma tsum_of_succ (c g : ℕ → ℂ) {w : ℂ} (h : Summable (fun k => c k * w ^ k))
    (h0 : g 0 = 0) (hsucc : ∀ n, g (n + 1) = c n) :
    (∑' k : ℕ, g k * w ^ k) = w * (∑' k : ℕ, c k * w ^ k) := by
  have hsh : HasSum (fun n : ℕ => g (n + 1) * w ^ (n + 1))
      ((∑' k : ℕ, c k * w ^ k) * w) := by
    have h' := HasSum.mul_right w h.hasSum
    simpa [hsucc, pow_succ, mul_assoc] using h'
  have hg : HasSum (fun k : ℕ => g k * w ^ k) ((∑' k : ℕ, c k * w ^ k) * w) := by
    have h' := (hasSum_nat_add_iff 1 (f := fun k : ℕ => g k * w ^ k)).mp hsh
    simpa [h0] using h'
  rw [hg.tsum_eq, mul_comm]

theorem tsum_shift_lemmas (W : PowerSeries ℚ) {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hW : ∀ k : ℕ, ‖((PowerSeries.coeff k W : ℚ) : ℂ)‖ * R ^ k ≤ C) (j : ℕ) {w : ℂ}
    (hw : ‖w‖ < R) :
    (w ^ j * (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.tq j W) : ℚ) : ℂ) * w ^ k)
        = (∑' k : ℕ, ((PowerSeries.coeff k W : ℚ) : ℂ) * w ^ k)
          - ∑ m ∈ Finset.range j, ((PowerSeries.coeff m W : ℚ) : ℂ) * w ^ m)
      ∧ ((∑' k : ℕ, ((PowerSeries.coeff k ((PowerSeries.X : PowerSeries ℚ) * W) : ℚ) : ℂ) * w ^ k)
        = w * (∑' k : ℕ, ((PowerSeries.coeff k W : ℚ) : ℂ) * w ^ k)) := by
  have hsum : Summable (fun k : ℕ => ((PowerSeries.coeff k W : ℚ) : ℂ) * w ^ k) :=
    summable_of_rate_bound hC hR hW hw
  constructor
  · simp only [Submission.CDTPlan.tq, PowerSeries.coeff_mk]
    exact tsum_shift_mul (fun k : ℕ => ((PowerSeries.coeff k W : ℚ) : ℂ)) hsum j
  · exact tsum_of_succ (fun k : ℕ => ((PowerSeries.coeff k W : ℚ) : ℂ))
      (fun k : ℕ => ((PowerSeries.coeff k ((PowerSeries.X : PowerSeries ℚ) * W) : ℚ) : ℂ))
      hsum (by simp [PowerSeries.coeff_zero_X_mul])
      (fun n => by simp [PowerSeries.coeff_succ_X_mul])

end Work.C17I
