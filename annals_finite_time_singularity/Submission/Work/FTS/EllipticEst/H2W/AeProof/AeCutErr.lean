import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.AngularW.cutZ2Deriv2
import Submission.Work.FTS.EllipticEst.weight_algebra_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeProof

open scoped Topology
open Filter MeasureTheory

/-!
## The truncation error of the radial cut-off family `cut n`, with the weight `w`

This file proves `AeCutErr`: for a nonnegative measurable `E` with `E ∈ L¹(Iz)` and
`w²E ∈ L¹(Iz)` (where `w z = (1+z)²/z²`), the truncation error

`Err n = ∫_z (2|(cut n)'| |(z²w²)'| + |(cut n)''| z²w²) E + ∫_z |(cut n)'| (z w²) E`

tends to `0`.

The proof does not need the (fine) structure of the two transition bands of `cut n`.
It uses only

* the two *uniform* bounds `|z (cut n)'(z)| ≤ K` and `|z² (cut n)''(z)| ≤ K₂`
  (`AngSecond.cut_deriv_uniform`, `AngularW.cutZ2Deriv2`), which together with
  `|(z²w²)'| ≤ 2 z w²` bound the integrand *globally* by `(5K + K₂) w² E`
  (the only place where `z > 0` is needed, the point `z = 0` being harmless);
* the pointwise convergence `(cut n)'(z) → 0`, `(cut n)''(z) → 0` for every fixed `z ≠ 0`,
  which follows from the *local constancy* of `cut n` at `z` for large `n`
  (`cut n ≡ 1` near `z > 0`, `cut n ≡ 0` near `z < 0`).

Dominated convergence with the integrable dominating function `(5K + K₂) w² E` then gives
the result.
-/

/-- `cut n` is identically `0` on a neighbourhood of every point `z < 1/(n+1)`. -/
private theorem cut_eventuallyEq_zero_of_lt (n : ℕ) {z : ℝ} (hz : z < 1 / ((n : ℝ) + 1)) :
    Work.FTS.EllipticEst.cut n =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
  have hpos : 0 < 1 / ((n : ℝ) + 1) - z := by linarith
  filter_upwards [Metric.ball_mem_nhds z hpos] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  exact Work.FTS.EllipticEst.cut_apply_zero_of_le n (by
    have := (abs_lt.mp hy).2
    linarith)

/-- `cut n` is identically `1` on a neighbourhood of every point of the interval
`(2/(n+1), 2(n+1))`. -/
private theorem cut_eventuallyEq_one_of_mid (n : ℕ) {z : ℝ} (h1 : 2 / ((n : ℝ) + 1) < z)
    (h2 : z < 2 * ((n : ℝ) + 1)) :
    Work.FTS.EllipticEst.cut n =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
  have hpos : 0 < min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z) / 2 := by
    have h : 0 < min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z) :=
      lt_min (by linarith) (by linarith)
    linarith
  filter_upwards [Metric.ball_mem_nhds z hpos] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hya := (abs_lt.mp hy).1
  have hyb := (abs_lt.mp hy).2
  have hm1 := min_le_left (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z)
  have hm2 := min_le_right (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z)
  exact Work.FTS.EllipticEst.cut_eq_one_of_mem n (by linarith) (by linarith)

/-- If `cut n` is locally constant near `z`, then both its first and its second derivative
vanish at `z`. -/
private theorem cut_derivs_eq_zero_of_eventuallyEq {n : ℕ} {z c : ℝ}
    (h : Work.FTS.EllipticEst.cut n =ᶠ[𝓝 z] (fun _ => c)) :
    deriv (Work.FTS.EllipticEst.cut n) z = 0 ∧
      deriv (deriv (Work.FTS.EllipticEst.cut n)) z = 0 := by
  constructor
  · rw [h.deriv_eq, deriv_const]
  · rw [h.deriv.deriv_eq]
    simp [deriv_const]

/-- For a fixed `z > 0` the derivatives of `cut n` vanish at `z` for all large `n` (there
`cut n ≡ 1` on a neighbourhood of `z`). -/
private theorem eventually_cut_derivs_eq_zero {z : ℝ} (hz : 0 < z) :
    ∀ᶠ n : ℕ in atTop,
      deriv (Work.FTS.EllipticEst.cut n) z = 0 ∧
        deriv (deriv (Work.FTS.EllipticEst.cut n)) z = 0 := by
  have hsmall : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
    simpa only [mul_zero, mul_one_div] using h
  have h1 : ∀ᶠ n : ℕ in atTop, 2 / ((n : ℝ) + 1) < z := (tendsto_order.1 hsmall).2 z hz
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add
      tendsto_const_nhds
  have hbig : ∀ᶠ n : ℕ in atTop, 2 * ((n : ℝ) + 1) > z := by
    have h3 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)) atTop atTop :=
      hbase.const_mul_atTop (by norm_num)
    have := (tendsto_atTop.1 h3) (z + 1)
    filter_upwards [this] with n hn
    linarith
  filter_upwards [h1, hbig] with n hn1 hn2
  exact cut_derivs_eq_zero_of_eventuallyEq (cut_eventuallyEq_one_of_mid n hn1 hn2)

/-- `|(z²w²)'| ≤ 2 z w²` for `z > 0`. -/
private theorem abs_deriv_zsq_w_sq_le (z : ℝ) (hz : 0 < z) :
    |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
      ≤ 2 * (Work.Spaces.w z) ^ 2 * z := by
  have hz3 : (0 : ℝ) < z ^ 3 := by positivity
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have h1z3 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  rw [Work.FTS.EllipticEst.weight_algebra_fts.2.2.1 z (ne_of_gt hz), abs_div, abs_of_pos hz3,
    div_le_iff₀ hz3, Work.Spaces.w]
  rw [show (2 : ℝ) * ((1 + z) ^ 2 / z ^ 2) ^ 2 * z * z ^ 3 = 2 * (1 + z) ^ 4 by
    field_simp]
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (le_of_lt h1z3)]
  have habs : |z - 1| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
  calc (2 * |z - 1|) * (1 + z) ^ 3 ≤ (2 * (1 + z)) * (1 + z) ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (le_of_lt h1z3)
    _ = 2 * (1 + z) ^ 4 := by ring

/-! ### Measurability of the two integrands -/

private theorem measurable_zsq_w_sq : Measurable (fun z : ℝ => z ^ 2 * (Work.Spaces.w z) ^ 2) := by
  refine (measurable_id.pow_const 2).mul ?_
  have h : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
  rw [h]
  exact (((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)).pow_const 2

private theorem measurable_z_mul_w_sq : Measurable (fun z : ℝ => z * (Work.Spaces.w z) ^ 2) := by
  refine measurable_id.mul ?_
  have h : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
  rw [h]
  exact (((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)).pow_const 2

private theorem aestronglyMeasurable_aeCutErr1 (n : ℕ) {E : ℝ → ℝ}
    (hEm : MeasureTheory.AEStronglyMeasurable E (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ =>
        (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hg : Measurable (fun z : ℝ =>
        (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))) := by
    refine Measurable.add ?_ ?_
    · exact (measurable_const.mul (measurable_deriv (Work.FTS.EllipticEst.cut n)).abs).mul
        (measurable_deriv (fun z : ℝ => z ^ 2 * (Work.Spaces.w z) ^ 2)).abs
    · exact ((measurable_deriv (deriv (Work.FTS.EllipticEst.cut n))).abs).mul measurable_zsq_w_sq
  exact MeasureTheory.AEStronglyMeasurable.mul hg.aestronglyMeasurable hEm

private theorem aestronglyMeasurable_aeCutErr2 (n : ℕ) {E : ℝ → ℝ}
    (hEm : MeasureTheory.AEStronglyMeasurable E (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => |deriv (Work.FTS.EllipticEst.cut n) z|
              * (z * (Work.Spaces.w z) ^ 2) * E z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hg : Measurable (fun z : ℝ => |deriv (Work.FTS.EllipticEst.cut n) z|
              * (z * (Work.Spaces.w z) ^ 2)) :=
    ((measurable_deriv (Work.FTS.EllipticEst.cut n)).abs).mul measurable_z_mul_w_sq
  exact MeasureTheory.AEStronglyMeasurable.mul hg.aestronglyMeasurable hEm

/-! ### The pointwise domination -/

/-- The first integrand of `AeCutErr` is dominated by `C · w² · E`. -/
private theorem aeCutErr_bound1 (E : ℝ → ℝ) (hE0 : ∀ z, 0 ≤ E z) {K K2 C : ℝ}
    (hCpos : 0 < C) (hC : 4 * K + K2 ≤ C)
    (hK : ∀ (n : ℕ) (z : ℝ), |z * deriv (Work.FTS.EllipticEst.cut n) z| ≤ K)
    (hK2 : ∀ (n : ℕ) (z : ℝ), |z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.cut n)) z| ≤ K2) :
    ∀ (n : ℕ) (z : ℝ),
      |(2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z| ≤ C * ((Work.Spaces.w z) ^ 2 * E z) := by
  intro n z
  by_cases hz : 0 < z
  · have hd1 : |deriv (Work.FTS.EllipticEst.cut n) z| * z ≤ K := by
      have h := hK n z
      rw [abs_mul, abs_of_pos hz] at h
      linarith [h]
    have hd2 : |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * z ^ 2 ≤ K2 := by
      have h := hK2 n z
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < z ^ 2 by positivity)] at h
      linarith [h]
    have hW := abs_deriv_zsq_w_sq_le z hz
    have e1 : 2 * |deriv (Work.FTS.EllipticEst.cut n) z|
        * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
        ≤ 4 * K * (Work.Spaces.w z) ^ 2 := by
      calc 2 * |deriv (Work.FTS.EllipticEst.cut n) z|
            * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
          ≤ 2 * |deriv (Work.FTS.EllipticEst.cut n) z|
            * (2 * (Work.Spaces.w z) ^ 2 * z) :=
            mul_le_mul_of_nonneg_left hW (by positivity)
        _ = (4 * (|deriv (Work.FTS.EllipticEst.cut n) z| * z)) * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ (4 * K) * (Work.Spaces.w z) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd1 (by norm_num)) (sq_nonneg _)
    have e2 : |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ K2 * (Work.Spaces.w z) ^ 2 := by
      calc |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
          = (|deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * z ^ 2) * (Work.Spaces.w z) ^ 2 := by
            ring
        _ ≤ K2 * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)
    have hnn : 0 ≤ 2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    rw [abs_of_nonneg (mul_nonneg hnn (hE0 z))]
    calc (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z
        ≤ ((4 * K + K2) * (Work.Spaces.w z) ^ 2) * E z :=
          mul_le_mul_of_nonneg_right (by linarith [e1, e2]) (hE0 z)
      _ = (4 * K + K2) * ((Work.Spaces.w z) ^ 2 * E z) := by ring
      _ ≤ C * ((Work.Spaces.w z) ^ 2 * E z) :=
          mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (hE0 z))
  · have hz0 : z < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨hd1, hd2⟩ :=
      cut_derivs_eq_zero_of_eventuallyEq (cut_eventuallyEq_zero_of_lt n hz0)
    rw [hd1, hd2]
    simp only [abs_zero, zero_mul, mul_zero, add_zero]
    exact mul_nonneg (le_of_lt hCpos) (mul_nonneg (sq_nonneg _) (hE0 z))

/-- The second integrand of `AeCutErr` is dominated by `C · w² · E`. -/
private theorem aeCutErr_bound2 (E : ℝ → ℝ) (hE0 : ∀ z, 0 ≤ E z) {K C : ℝ}
    (hCpos : 0 < C) (hC : K ≤ C)
    (hK : ∀ (n : ℕ) (z : ℝ), |z * deriv (Work.FTS.EllipticEst.cut n) z| ≤ K) :
    ∀ (n : ℕ) (z : ℝ),
      |(|deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)) * E z|
        ≤ C * ((Work.Spaces.w z) ^ 2 * E z) := by
  intro n z
  by_cases hz : 0 < z
  · have hd1 : |deriv (Work.FTS.EllipticEst.cut n) z| * z ≤ K := by
      have h := hK n z
      rw [abs_mul, abs_of_pos hz] at h
      linarith [h]
    have hnn : 0 ≤ |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) :=
      mul_nonneg (abs_nonneg _) (mul_nonneg (le_of_lt hz) (sq_nonneg _))
    rw [abs_of_nonneg (mul_nonneg hnn (hE0 z))]
    calc (|deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)) * E z
        ≤ (K * (Work.Spaces.w z) ^ 2) * E z :=
          mul_le_mul_of_nonneg_right (by
            calc |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)
                = (|deriv (Work.FTS.EllipticEst.cut n) z| * z) * (Work.Spaces.w z) ^ 2 := by ring
              _ ≤ K * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hd1 (sq_nonneg _))
            (hE0 z)
      _ = K * ((Work.Spaces.w z) ^ 2 * E z) := by ring
      _ ≤ C * ((Work.Spaces.w z) ^ 2 * E z) :=
          mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (hE0 z))
  · have hz0 : z < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨hd1, _⟩ :=
      cut_derivs_eq_zero_of_eventuallyEq (cut_eventuallyEq_zero_of_lt n hz0)
    rw [hd1]
    simp only [abs_zero, zero_mul]
    exact mul_nonneg (le_of_lt hCpos) (mul_nonneg (sq_nonneg _) (hE0 z))

/-! ### The pointwise convergence -/

private theorem aeCutErr_lim1 (E : ℝ → ℝ) :
    ∀ z : ℝ, Tendsto (fun n : ℕ =>
        (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z) atTop (nhds 0) := by
  intro z
  by_cases hz : 0 < z
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_cut_derivs_eq_zero hz] with n hn
    rw [hn.1, hn.2]
    ring
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    have hz0 : z < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨hd1, hd2⟩ :=
      cut_derivs_eq_zero_of_eventuallyEq (cut_eventuallyEq_zero_of_lt n hz0)
    rw [hd1, hd2]
    ring

private theorem aeCutErr_lim2 (E : ℝ → ℝ) :
    ∀ z : ℝ, Tendsto (fun n : ℕ =>
        (|deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)) * E z)
      atTop (nhds 0) := by
  intro z
  by_cases hz : 0 < z
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_cut_derivs_eq_zero hz] with n hn
    rw [hn.1]
    ring
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    have hz0 : z < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨hd1, _⟩ :=
      cut_derivs_eq_zero_of_eventuallyEq (cut_eventuallyEq_zero_of_lt n hz0)
    rw [hd1]
    ring

/-- **The truncation error of the radial cut-off family tends to zero.**

For a nonnegative `E` on `Iz = [0,∞)` which is `AEStronglyMeasurable` and satisfies
`E, w²E ∈ L¹(Iz)` (`w z = (1+z)²/z²`), the truncation error made by the `n`-th cut-off `cut n`
in the radial integration by parts,

`Err n = ∫_z (2|(cut n)'| |(z²w²)'| + |(cut n)''| z²w²) E + ∫_z |(cut n)'| (z w²) E`,

tends to `0` as `n → ∞`.

Proof: the two uniform bounds `|z (cut n)'(z)| ≤ K` (`AngSecond.cut_deriv_uniform`) and
`|z²(cut n)''(z)| ≤ K₂` (`AngularW.cutZ2Deriv2`), together with `|(z²w²)'| ≤ 2 z w²`, dominate
the integrand by `(5K + K₂) w² E` — an integrable function.  For fixed `z > 0` the cut-off is
eventually equal to `1` near `z` (`cut_eq_one_of_mem`), so both derivatives vanish at `z` for
large `n`, while for `z ≤ 0` the cut-off is eventually (indeed always) `0` near `z`.  Hence the
integrand converges pointwise to `0` and dominated convergence applies. -/
theorem AeCutErr (E : ℝ → ℝ) (hE0 : ∀ z, 0 ≤ E z)
    (hEm : MeasureTheory.AEStronglyMeasurable E (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hE1 : MeasureTheory.IntegrableOn E Work.Spaces.Iz)
    (hE2 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * E z) Work.Spaces.Iz) :
    Filter.Tendsto (fun n : ℕ =>
        (∫ z in Work.Spaces.Iz, (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z)
        + (∫ z in Work.Spaces.Iz, |deriv (Work.FTS.EllipticEst.cut n) z|
              * (z * (Work.Spaces.w z) ^ 2) * E z))
      Filter.atTop (nhds 0) := by
  -- `hE1` is not needed: the domination only uses `w²E ∈ L¹`.
  have hE1int : MeasureTheory.IntegrableOn E Work.Spaces.Iz := hE1
  obtain ⟨K, hKpos, hKbd, -, -⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  obtain ⟨K2, hK2pos, hK2bd⟩ := Work.FTS.EllipticEst.AngularW.cutZ2Deriv2
  have hCpos : (0 : ℝ) < 20 * (K + K2 + 1) := by positivity
  have hC1 : 4 * K + K2 ≤ 20 * (K + K2 + 1) := by linarith
  have hC2 : K ≤ 20 * (K + K2 + 1) := by linarith
  have hX : Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z) atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (F := fun n z =>
        (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * E z)
      (f := fun _ => (0 : ℝ))
      (fun z => 20 * (K + K2 + 1) * ((Work.Spaces.w z) ^ 2 * E z))
      (fun n => aestronglyMeasurable_aeCutErr1 n hEm)
      (hE2.const_mul (20 * (K + K2 + 1)))
      (fun n => Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        exact aeCutErr_bound1 E hE0 hCpos hC1 hKbd hK2bd n z))
      (Filter.Eventually.of_forall (aeCutErr_lim1 E))
    simpa using h
  have hY : Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        |deriv (Work.FTS.EllipticEst.cut n) z|
              * (z * (Work.Spaces.w z) ^ 2) * E z) atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (F := fun n z => (|deriv (Work.FTS.EllipticEst.cut n) z|
              * (z * (Work.Spaces.w z) ^ 2)) * E z)
      (f := fun _ => (0 : ℝ))
      (fun z => 20 * (K + K2 + 1) * ((Work.Spaces.w z) ^ 2 * E z))
      (fun n => aestronglyMeasurable_aeCutErr2 n hEm)
      (hE2.const_mul (20 * (K + K2 + 1)))
      (fun n => Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        exact aeCutErr_bound2 E hE0 hCpos hC2 hKbd n z))
      (Filter.Eventually.of_forall (aeCutErr_lim2 E))
    simpa using h
  simpa using hX.add hY

end Work.FTS.EllipticEst.H2W.AeProof
