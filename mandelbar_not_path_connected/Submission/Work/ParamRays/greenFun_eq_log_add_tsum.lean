/-
# The Green function of an escaping orbit as a logarithm plus a telescoping series

For `max 2 ‖c‖ < ‖w‖` the whole orbit of `w` stays outside the escape radius, and
the normalized logarithms telescope:

`2^{-N} log ‖T_c^[N] w‖ = log ‖w‖ + ∑_{n<N} 2^{-(n+1)} log (‖z_{n+1}‖ / ‖z_n‖²)`.

Since consecutive orbit norms satisfy `‖z_{n+1}‖ ≤ ‖z_n‖² + ‖c‖` and
`‖z_{n+1}‖ ≥ ‖z_n‖² - ‖c‖`, the ratio `‖z_{n+1}‖/‖z_n‖²` is bounded between `1/2`
and `2`, which makes the series absolutely convergent.  Passing to the limit gives

`greenFun c w = log ‖w‖ + ∑' n, 2^{-(n+1)} log (‖z_{n+1}‖ / ‖z_n‖²)`.

## Main results

* `Work.ParamRays.norm_le_norm_orbit` : the orbit stays outside the escape radius.
* `Work.ParamRays.abs_log_orbit_ratio_le` : `|log ‖z_{n+1}‖ - 2 log ‖z_n‖| ≤ log 2`.
* `Work.ParamRays.summable_orbitLog` : the series is summable.
* `Work.ParamRays.greenSeq_eq_log_add_sum` : the telescoping identity.
* `Work.ParamRays.greenFun_eq_log_add_tsum` : the Green function of an escaping
  point as the logarithm of its norm plus that series.
-/
import Mathlib
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Finset
open scoped Real Topology

namespace Work.ParamRays

/-- **The orbit stays outside the escape radius.**  If `max 2 ‖c‖ < ‖w‖` then
`‖w‖ ≤ ‖T_c^[n] w‖` for every `n`. -/
theorem norm_le_norm_orbit (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) (n : ℕ) :
    ‖w‖ ≤ ‖orbit c w n‖ := by
  have h2 : 2 < ‖w‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) h
  have hnn : 0 ≤ (n : ℝ) * (‖w‖ * (‖w‖ - 2)) :=
    mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (by linarith) (by linarith))
  have hge := norm_orbit_ge_add c w h n
  linarith

/-- If `max 2 ‖c‖ < ‖w‖` then no orbit point is the origin. -/
theorem orbit_norm_ne_zero (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) (n : ℕ) :
    ‖orbit c w n‖ ≠ 0 := by
  have h2 : 2 < ‖w‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) h
  have hge := norm_le_norm_orbit c w h n
  exact ne_of_gt (lt_of_lt_of_le (by linarith) hge)

/-- **The logarithmic ratio of consecutive orbit norms is bounded by `log 2`.**
Indeed `‖z_{n+1}‖/‖z_n‖² ∈ [1/2, 2]`. -/
theorem abs_log_orbit_ratio_le (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) (n : ℕ) :
    |Real.log ‖orbit c w (n + 1)‖ - 2 * Real.log ‖orbit c w n‖| ≤ Real.log 2 := by
  have h2 : 2 < ‖w‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) h
  have hcw : ‖c‖ < ‖w‖ := lt_of_le_of_lt (le_max_right 2 ‖c‖) h
  set r := ‖orbit c w n‖ with hr
  have hrn : ‖w‖ ≤ r := norm_le_norm_orbit c w h n
  have hr2 : 2 < r := lt_of_lt_of_le h2 hrn
  have hrpos : 0 < r := by linarith
  have hr2pos : 0 < r ^ 2 := pow_pos hrpos 2
  have hsq : r ^ 2 ≠ 0 := ne_of_gt hr2pos
  -- `‖c‖` is at most `r ^ 2 / 2` and hence at most `r ^ 2`
  have hc2 : ‖c‖ ≤ r ^ 2 / 2 := by
    have h1 : ‖w‖ ≤ ‖w‖ ^ 2 / 2 := by nlinarith
    have h2' : ‖w‖ ^ 2 / 2 ≤ r ^ 2 / 2 := by nlinarith
    linarith
  have hc3 : ‖c‖ ≤ r ^ 2 := by nlinarith
  have hlow : r ^ 2 - ‖c‖ ≤ ‖orbit c w (n + 1)‖ := by
    rw [orbit_succ, hr]
    exact norm_sq_sub_le_norm_Tantibar c (orbit c w n)
  have hup : ‖orbit c w (n + 1)‖ ≤ r ^ 2 + ‖c‖ := by
    rw [orbit_succ, hr]
    exact norm_Tantibar_le c (orbit c w n)
  have hlownn : 0 < r ^ 2 - ‖c‖ := by nlinarith
  have hspos : 0 < ‖orbit c w (n + 1)‖ := lt_of_lt_of_le hlownn hlow
  have hup' : Real.log ‖orbit c w (n + 1)‖ ≤ Real.log 2 + 2 * Real.log r := by
    have hle : ‖orbit c w (n + 1)‖ ≤ 2 * r ^ 2 := by
      have : r ^ 2 + ‖c‖ ≤ 2 * r ^ 2 := by nlinarith
      linarith
    calc Real.log ‖orbit c w (n + 1)‖ ≤ Real.log (2 * r ^ 2) :=
          Real.log_le_log hspos hle
      _ = Real.log 2 + 2 * Real.log r := by
          rw [Real.log_mul (by norm_num) hsq, Real.log_pow]
          push_cast
          ring
  have hlow' : 2 * Real.log r - Real.log 2 ≤ Real.log ‖orbit c w (n + 1)‖ := by
    have hle : r ^ 2 / 2 ≤ ‖orbit c w (n + 1)‖ := by
      have : r ^ 2 / 2 ≤ r ^ 2 - ‖c‖ := by nlinarith
      linarith
    calc 2 * Real.log r - Real.log 2 = Real.log (r ^ 2) - Real.log 2 := by
          rw [Real.log_pow]
          push_cast
          ring
      _ = Real.log (r ^ 2 / 2) := (Real.log_div hsq (by norm_num)).symm
      _ ≤ Real.log ‖orbit c w (n + 1)‖ := Real.log_le_log (by linarith) hle
  have hfin : |Real.log ‖orbit c w (n + 1)‖ - 2 * Real.log r| ≤ Real.log 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [hr] using hfin

/-- The telescoping terms of an escaping orbit form an absolutely convergent series. -/
theorem summable_orbitLog (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) :
    Summable fun n : ℕ =>
      ((2 : ℝ) ^ (n + 1))⁻¹ * Real.log (‖orbit c w (n + 1)‖ / ‖orbit c w n‖ ^ 2) := by
  have hgeom : Summable fun n : ℕ => ((1 / 2 : ℝ)) ^ n * Real.log 2 :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right (Real.log 2)
  refine Summable.of_norm_bounded hgeom fun n => ?_
  have hlogeq : Real.log (‖orbit c w (n + 1)‖ / ‖orbit c w n‖ ^ 2)
      = Real.log ‖orbit c w (n + 1)‖ - 2 * Real.log ‖orbit c w n‖ := by
    rw [Real.log_div (orbit_norm_ne_zero c w h (n + 1))
      (pow_ne_zero 2 (orbit_norm_ne_zero c w h n)), Real.log_pow]
    push_cast
    ring
  calc ‖((2 : ℝ) ^ (n + 1))⁻¹ * Real.log (‖orbit c w (n + 1)‖ / ‖orbit c w n‖ ^ 2)‖
      = ((2 : ℝ) ^ (n + 1))⁻¹ * |Real.log (‖orbit c w (n + 1)‖ / ‖orbit c w n‖ ^ 2)| := by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ (n + 1))⁻¹)]
    _ = ((2 : ℝ) ^ (n + 1))⁻¹
          * |Real.log ‖orbit c w (n + 1)‖ - 2 * Real.log ‖orbit c w n‖| := by
        rw [hlogeq]
    _ ≤ ((2 : ℝ) ^ (n + 1))⁻¹ * Real.log 2 :=
        mul_le_mul_of_nonneg_left (abs_log_orbit_ratio_le c w h n) (by positivity)
    _ ≤ ((1 / 2 : ℝ)) ^ n * Real.log 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by norm_num))
        have hp : ((2 : ℝ) ^ (n + 1))⁻¹ = ((1 / 2 : ℝ)) ^ n * (1 / 2) := by
          rw [← inv_pow, show ((2 : ℝ))⁻¹ = 1 / 2 by norm_num, pow_succ]
        rw [hp]
        exact mul_le_of_le_one_right (pow_nonneg (by norm_num) n) (by norm_num)

/-- **Telescoping identity.**  For an escaping orbit the partial sums of the
series are exactly the normalized logarithm minus `log ‖w‖`. -/
theorem greenSeq_eq_log_add_sum (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) (N : ℕ) :
    greenSeq c w N = Real.log ‖w‖ + ∑ i ∈ Finset.range N,
      ((2 : ℝ) ^ (i + 1))⁻¹ * Real.log (‖orbit c w (i + 1)‖ / ‖orbit c w i‖ ^ 2) := by
  have h2 : 2 < ‖w‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) h
  have hlogeq : ∀ i : ℕ, Real.log (‖orbit c w (i + 1)‖ / ‖orbit c w i‖ ^ 2)
      = Real.log ‖orbit c w (i + 1)‖ - 2 * Real.log ‖orbit c w i‖ := fun i => by
    rw [Real.log_div (orbit_norm_ne_zero c w h (i + 1))
      (pow_ne_zero 2 (orbit_norm_ne_zero c w h i)), Real.log_pow]
    push_cast
    ring
  have htel : ∑ i ∈ Finset.range N,
        ((2 : ℝ) ^ (i + 1))⁻¹ * Real.log (‖orbit c w (i + 1)‖ / ‖orbit c w i‖ ^ 2)
      = ((2 : ℝ) ^ N)⁻¹ * Real.log ‖orbit c w N‖ - Real.log ‖w‖ := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hlogeq N]
      have hp : ((2 : ℝ) ^ N)⁻¹ = 2 * ((2 : ℝ) ^ (N + 1))⁻¹ := by
        rw [pow_succ, mul_inv]
        ring
      rw [hp]
      ring
  rw [greenSeq, htel]
  have hposlog : log⁺ ‖orbit c w N‖ = Real.log ‖orbit c w N‖ := by
    refine Real.posLog_eq_log ?_
    rw [abs_of_nonneg (norm_nonneg _)]
    linarith [norm_le_norm_orbit c w h N]
  rw [hposlog]
  ring

/-- **The Green function of an escaping point.**  For `max 2 ‖c‖ < ‖w‖`,

`G_c(w) = log ‖w‖ + ∑_{n ≥ 0} 2^{-(n+1)} log (‖T_c^{n+1} w‖ / ‖T_c^n w‖²)`. -/
theorem greenFun_eq_log_add_tsum (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) :
    Work.ParamRays.greenFun c w = Real.log ‖w‖ +
      ∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ *
        Real.log (‖Work.ParamRays.orbit c w (n + 1)‖ / ‖Work.ParamRays.orbit c w n‖ ^ 2) := by
  have hsum := summable_orbitLog c w h
  have htend : Tendsto (fun N : ℕ => Real.log ‖w‖ + ∑ i ∈ Finset.range N,
        ((2 : ℝ) ^ (i + 1))⁻¹ *
          Real.log (‖orbit c w (i + 1)‖ / ‖orbit c w i‖ ^ 2)) atTop
      (𝓝 (Real.log ‖w‖ + ∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ *
          Real.log (‖orbit c w (n + 1)‖ / ‖orbit c w n‖ ^ 2))) :=
    hsum.hasSum.tendsto_sum_nat.const_add _
  refine greenFun_eq_of_tendsto (htend.congr fun N => ?_)
  exact (greenSeq_eq_log_add_sum c w h N).symm

end Work.ParamRays
