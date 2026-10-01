import Mathlib
import Submission.Work.LinnikAreas.DhRepel.eventuallyMulLogPowLeRpow
import Submission.Work.LinnikAreas.DhRepel.rpowBaseLeLogLogPow

namespace Work.LinnikAreas.DhRepel

/-- **Log-free arithmetic estimate.**  For all `C > 0` and `A > 0` there is `q₀` such that for every
`q ≥ q₀` and every `t` with `0 ≤ t ≤ (1/3) log log log q`,

  `C · (q · 10 log q)^{3t/log q} ≤ (log q)^A`.

This is the numerical input that makes the near-line zero count of a single Dirichlet character
*log-free*: Jutila's estimate with `ε = 1`, `T = 10 log q` and `σ = 1 - t/log q` bounds the count by
`C_J (q·10 log q)^{3t/log q}`, and since `3t ≤ log log log q` the latter is `≪ C_J log log q`, which
`(log q)^A` dominates for every fixed `A > 0` (no restriction `A < 1` is needed here). -/
theorem rpowArithLogFree (C A : ℝ) (hC : 0 < C) (hA : 0 < A) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ t : ℝ, 0 ≤ t →
      t ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      C * ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ (3 * t / Real.log (q : ℝ))
        ≤ (Real.log (q : ℝ)) ^ A := by
  -- `log q → ∞`, so eventually `log q ≥ 100`
  have hlog : ∀ᶠ q : ℕ in Filter.atTop, 100 ≤ Real.log (q : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 100)
  -- `log`-powers are eventually dominated by any positive power
  have hdom : ∀ᶠ q : ℕ in Filter.atTop,
      C * (Real.log (Real.log (q : ℝ))) ^ 11 ≤ (Real.log (q : ℝ)) ^ A :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventuallyMulLogPowLeRpow C A 11 hC hA)
  -- combine the two eventual statements into a single threshold
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (hlog.and hdom)
  refine ⟨q₀, fun q hq t ht0 htle => ?_⟩
  obtain ⟨hL, hdomq⟩ := hq₀ q hq
  -- the hypothesis `t ≤ (1/3) log log log q` gives `3t ≤ log log log q`
  have htZ : 3 * t ≤ Real.log (Real.log (Real.log (q : ℝ))) := by linarith
  -- the pure power bound
  have hpow := rpowBaseLeLogLogPow q t hL ht0 htZ
  calc C * ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ (3 * t / Real.log (q : ℝ))
      ≤ C * (Real.log (Real.log (q : ℝ))) ^ 11 :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
    _ ≤ (Real.log (q : ℝ)) ^ A := hdomq

end Work.LinnikAreas.DhRepel
