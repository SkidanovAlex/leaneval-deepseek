import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

/-- The function `Y ↦ C * (log Y)^c * (log log Y)^k * exp(-lam * log log Y)` tends to `0`
as `Y → +∞`, whenever `c < lam`.

The point is that `log log Y → +∞`, and on the logarithmic scale the factor
`(log Y)^c = exp(c · log log Y)` is absorbed into the exponential, leaving
`C · (log log Y)^k · exp((c - lam) · log log Y)`, an exponential of negative rate
times a polynomial term, which decays to `0`. -/
theorem tendsto_loglog_exp_neg_mul (C c k lam : ℝ) (hc : c < lam) (hlam : 0 < lam) :
    Filter.Tendsto (fun Y : ℝ => C * (Real.log Y) ^ c * (Real.log (Real.log Y)) ^ k *
      Real.exp (-lam * Real.log (Real.log Y))) Filter.atTop (nhds 0) := by
  -- Recombine the two exponentials on the logarithmic scale.
  have key : ∀ t : ℝ, C * (t ^ k * Real.exp (-(lam - c) * t))
      = C * Real.exp (t * c) * t ^ k * Real.exp (-lam * t) := by
    intro t
    have hexp : Real.exp (t * c) * Real.exp (-lam * t) = Real.exp (-(lam - c) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← hexp]; ring
  -- `log (log Y) → +∞`.
  have hll : Filter.Tendsto (fun Y : ℝ => Real.log (Real.log Y)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  -- `t^k * exp (-(lam - c) t) → 0`, since `lam - c > 0`.
  have hmain : Filter.Tendsto
      (fun t : ℝ => C * (t ^ k * Real.exp (-(lam - c) * t))) Filter.atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k (lam - c) (sub_pos.mpr hc)
    simpa using h.const_mul C
  refine (hmain.comp hll).congr' ?_
  -- Eventually `(log Y)^c = exp (c · log log Y)`, and the two expressions agree.
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with Y hY
  have hpos : 0 < Real.log Y := Real.log_pos hY
  simp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos hpos]
  exact key (Real.log (Real.log Y))

end Work.BMF.mr_core
