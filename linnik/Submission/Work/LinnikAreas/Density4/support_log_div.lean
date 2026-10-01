import Mathlib

namespace Work.LinnikAreas.Density4

/-- If `f` vanishes on `[x₀, ∞)` and `M > exp(x₀ L)` with `L > 0`, then for every `n ≥ M`, the
argument `log n / L` lies in `[x₀, ∞)`, so `f (log n / L) = 0`. -/
lemma support_log_div {x₀ L : ℝ} (hL : 0 < L) (hx₀ : 0 < x₀) {f : ℝ → ℝ}
    (hfs : ∀ t, x₀ ≤ t → f t = 0) {M : ℕ} (hM : Real.exp (x₀ * L) < (M : ℝ)) {n : ℕ}
    (hn : M ≤ n) : f (Real.log n / L) = 0 := by
  apply hfs
  -- It suffices to show `x₀ * L ≤ log n`, then divide by `L > 0`.
  rw [le_div_iff₀ hL]
  have hexp_pos : 0 < Real.exp (x₀ * L) := Real.exp_pos _
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_trans hexp_pos hM
  -- `log (exp (x₀ * L)) < log M` and `log M ≤ log n`.
  have hlog_lt : Real.log (Real.exp (x₀ * L)) < Real.log (M : ℝ) :=
    Real.log_lt_log hexp_pos hM
  rw [Real.log_exp] at hlog_lt
  have hMn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog_le : Real.log (M : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log hMpos hMn
  linarith

end Work.LinnikAreas.Density4
