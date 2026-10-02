import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace Commons.Analysis.Real

/-- **Exponential decay beats a linear polynomial.**  For `a, b ≥ 0` and `c > 0`
there is `N` with `(a n + b) * exp (-(c n)) < 1` for all `n ≥ N`. -/
theorem exists_mul_exp_neg_lt_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ n ≥ N, (a * (n : ℝ) + b) * Real.exp (-(c * (n : ℝ))) < 1 := by
  have hlim : Filter.Tendsto (fun x : ℝ => (a * x + b) * Real.exp (-(c * x)))
      Filter.atTop (𝓝 0) := by
    have hbase : Filter.Tendsto (fun x : ℝ => x * Real.exp (-(c * x))) Filter.atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
      simpa only [Real.rpow_one, neg_mul] using h
    have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (-(c * x))) Filter.atTop (𝓝 0) := by
      have h : Filter.Tendsto (fun x : ℝ => c * x) Filter.atTop Filter.atTop :=
        Filter.tendsto_id.const_mul_atTop' hc
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h
    have h := (hbase.const_mul a).add (hexp.const_mul b)
    simp only [mul_zero, add_zero] at h
    exact h.congr' (by filter_upwards with x; ring)
  have hev : ∀ᶠ x : ℝ in Filter.atTop, (a * x + b) * Real.exp (-(c * x)) < 1 :=
    hlim.eventually_lt_const zero_lt_one
  rcases Filter.eventually_atTop.1 hev with ⟨M, hM⟩
  exact ⟨Nat.ceil M, fun n hn => hM (n : ℝ) (Nat.ceil_le.1 hn)⟩

end Commons.Analysis.Real