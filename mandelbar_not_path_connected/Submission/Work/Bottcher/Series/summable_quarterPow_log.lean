import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Summability of `Σ 4^{-(n+1)} log (f n)` for `f n → 1`

A general analytic input reused by the Böttcher-series chapter: if `f : ℕ → ℂ`
converges to `1`, then the series `Σ_n 4^{-(n+1)} log (f n)` converges.  Indeed
`Complex.log` is continuous at `1` (which lies in the slit plane, where the
principal branch is holomorphic), so `log (f n) → log 1 = 0`; in particular
`‖log (f n)‖` is eventually `≤ 1`, and comparison with the geometric series
`Σ 4^{-(n+1)}` gives absolute convergence.
-/

open Filter

namespace Work.Bottcher.Series

theorem summable_quarterPow_log (f : ℕ → ℂ) (hf : Filter.Tendsto f Filter.atTop (nhds 1)) :
    Summable (fun n : ℕ => (((1 / 4 : ℝ) ^ (n + 1) : ℝ) : ℂ) * Complex.log (f n)) := by
  -- `Complex.log` is continuous at `1 ∈ slitPlane`, so `log (f n) → 0`.
  have hlog : Tendsto (fun n : ℕ => Complex.log (f n)) atTop (nhds 0) := by
    have h := hf.clog Complex.one_mem_slitPlane
    simpa using h
  -- Hence `‖log (f n)‖ ≤ 1` eventually.
  have hev : ∀ᶠ n : ℕ in atTop, ‖Complex.log (f n)‖ ≤ 1 := by
    have h0 := tendsto_zero_iff_norm_tendsto_zero.mp hlog
    filter_upwards [h0.eventually (Iio_mem_nhds zero_lt_one)] with n hn
    exact le_of_lt hn
  -- Compare with the geometric series `Σ 4^{-(n+1)}`.
  refine Summable.of_norm_bounded_eventually (g := fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) ?_ ?_
  · have h0 : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    simpa [pow_succ] using h0.mul_right (1 / 4 : ℝ)
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with n hn
    rw [norm_mul]
    have hnorm : ‖(((1 / 4 : ℝ) ^ (n + 1) : ℝ) : ℂ)‖ = (1 / 4 : ℝ) ^ (n + 1) := by simp
    rw [hnorm]
    calc (1 / 4 : ℝ) ^ (n + 1) * ‖Complex.log (f n)‖
        ≤ (1 / 4 : ℝ) ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left hn (by positivity)
      _ = (1 / 4 : ℝ) ^ (n + 1) := mul_one _

end Work.Bottcher.Series
