import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.Analysis.ExpLog.log_le_two_sqrt

namespace Commons.Analysis.ExpLog

/-- For every nonnegative `z`, `exp z ≥ z²/4`.

Proof: `exp z = (exp (z/2))²`, while `exp(z/2) ≥ 1 + z/2 ≥ z/2 ≥ 0`, so
squaring gives `exp z ≥ (z/2)² = z²/4`. -/
lemma exp_ge_sq_div_four (z : ℝ) (hz : 0 ≤ z) : z ^ 2 / 4 ≤ Real.exp z := by
  have hz2 : 0 ≤ z / 2 := by positivity
  have h1 : 1 + z / 2 ≤ Real.exp (z / 2) := by
    simpa [add_comm] using Real.add_one_le_exp (z / 2)
  have h2 : 0 ≤ 1 + z / 2 := by positivity
  have hz2le : z / 2 ≤ 1 + z / 2 := by linarith
  have hsq1 : (z / 2) ^ 2 ≤ (1 + z / 2) ^ 2 := by
    exact pow_le_pow_left₀ hz2 hz2le 2
  have hsq2 : (1 + z / 2) ^ 2 ≤ (Real.exp (z / 2)) ^ 2 := by
    exact pow_le_pow_left₀ h2 h1 2
  calc
    z ^ 2 / 4 = (z / 2) ^ 2 := by ring
    _ ≤ (1 + z / 2) ^ 2 := hsq1
    _ ≤ (Real.exp (z / 2)) ^ 2 := hsq2
    _ = Real.exp z := by
      rw [pow_two, ← Real.exp_add, add_halves]

/-- For `u ≥ 1000`, `log u ≤ u/8`.

Proof: taking exponentials reduces this to `u ≤ exp(u/8)`, and
`exp(u/8) ≥ (u/8)²/4 = u²/256 ≥ u` since `u ≥ 256`. -/
lemma log_le_div_eight_of_ge (u : ℝ) (hu : 1000 ≤ u) : Real.log u ≤ u / 8 := by
  have hu0 : 0 < u := by linarith
  rw [Real.log_le_iff_le_exp hu0]
  have hz : 0 ≤ u / 8 := by positivity
  have he : u ^ 2 / 256 ≤ Real.exp (u / 8) := by
    have h := exp_ge_sq_div_four (u / 8) hz
    convert h using 1
    ring
  have hmain : u ≤ u ^ 2 / 256 := by
    have hprod : 0 ≤ u * (u - 256) := mul_nonneg hu0.le (by linarith)
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 256)]
    nlinarith [hprod]
  exact le_trans hmain he

/-- If `x ≥ 10^6` then `1000 ≤ √x`. -/
lemma sqrt_ge_1000_of_ge {x : ℝ} (hx : (1000000 : ℝ) ≤ x) : (1000 : ℝ) ≤ Real.sqrt x := by
  have hsq : (1000 : ℝ) ^ 2 ≤ x := by
    norm_num at hx ⊢
    exact hx
  have hmono : Real.sqrt ((1000 : ℝ) ^ 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt hsq
  norm_num at hmono
  exact hmono

/-- For `x ≥ 0`, `√(x+1) ≤ √x + 1`. -/
lemma sqrt_add_one_le_sqrt_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (x + 1) ≤ Real.sqrt x + 1 := by
  have ha : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
  have hb : 0 ≤ Real.sqrt x + 1 := by positivity
  have hsq : (Real.sqrt (x + 1)) ^ 2 ≤ (Real.sqrt x + 1) ^ 2 := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ x + 1)]
    rw [add_sq, Real.sq_sqrt hx]
    nlinarith [Real.sqrt_nonneg x]
  exact (sq_le_sq₀ ha hb).mp hsq

/-- For `s ≥ 1000`, `2s + 2 ≤ (7/400)·s²`. -/
lemma seven_fourhundred_sq_ge_two_s_add_two (s : ℝ) (hs : 1000 ≤ s) :
    2 * s + 2 ≤ (7 / 400 : ℝ) * s ^ 2 := by
  have hs0 : 0 ≤ s := by linarith
  have h1 : 1000 * s ≤ s * s := by
    have hprod : 0 ≤ s * (s - 1000) := mul_nonneg hs0 (by linarith)
    nlinarith
  calc
    2 * s + 2 ≤ (35 / 2 : ℝ) * s := by linarith
    _ = (7 / 400 : ℝ) * (1000 * s) := by ring
    _ ≤ (7 / 400 : ℝ) * (s * s) := by
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = (7 / 400 : ℝ) * s ^ 2 := by ring

/-- The tail of the `log`-band bound: for `x ≥ 10^6`,

`log (x+1) + 2√x · log x ≤ (3/4)·log 2 · x`.

With `s = √x ≥ 1000` one has `log s ≤ s/8` (`log_le_div_eight_of_ge`), hence
`2√x·log x = 4s·log s ≤ 4s·(s/8) = x/2`.  The remaining term satisfies
`log (x+1) ≤ 2√(x+1) ≤ 2s + 2 ≤ (3/4·log 2 − 1/2)·x`, where the last step is
the elementary inequality `2s + 2 ≤ (7/400)·s²` (valid for `s ≥ 1000`)
combined with `(3/4)·log 2 − 1/2 ≥ 7/400` (`log 2 > 0.6931471803`). -/
theorem log_band_tail {x : ℝ} (hx : (1000000 : ℝ) ≤ x) :
    Real.log (x + 1) + 2 * √x * Real.log x ≤ (3 / 4) * Real.log 2 * x := by
  have hx0 : 0 < x := by linarith
  have hx0le : 0 ≤ x := le_of_lt hx0
  have hsqrt1000 : (1000 : ℝ) ≤ Real.sqrt x := sqrt_ge_1000_of_ge hx
  have hlogsqrt : Real.log (Real.sqrt x) ≤ Real.sqrt x / 8 :=
    log_le_div_eight_of_ge (Real.sqrt x) hsqrt1000
  have hlogx : Real.log x = 2 * Real.log (Real.sqrt x) := by
    have h := Real.log_sqrt hx0le
    linarith
  have hA : 2 * Real.sqrt x * Real.log x ≤ x / 2 := by
    calc
      2 * Real.sqrt x * Real.log x = 4 * Real.sqrt x * Real.log (Real.sqrt x) := by
        rw [hlogx]
        ring
      _ ≤ 4 * Real.sqrt x * (Real.sqrt x / 8) := by
        exact mul_le_mul_of_nonneg_left hlogsqrt (by positivity)
      _ = x / 2 := by
        rw [show 4 * Real.sqrt x * (Real.sqrt x / 8) = (Real.sqrt x) ^ 2 / 2 by ring]
        rw [Real.sq_sqrt hx0le]
  have hB : Real.log (x + 1) ≤ 2 * Real.sqrt x + 2 := by
    calc
      Real.log (x + 1) ≤ 2 * Real.sqrt (x + 1) :=
        log_le_two_sqrt (by linarith : 0 ≤ x + 1)
      _ ≤ 2 * (Real.sqrt x + 1) := by
        exact mul_le_mul_of_nonneg_left (sqrt_add_one_le_sqrt_add hx0le) (by norm_num)
      _ = 2 * Real.sqrt x + 2 := by ring
  have hδ : (7 / 400 : ℝ) ≤ (3 / 4) * Real.log 2 - 1 / 2 := by
    have hlog2 : 0.6931471803 ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9
    linarith
  have hC : 2 * Real.sqrt x + 2 ≤ ((3 / 4) * Real.log 2 - 1 / 2) * x := by
    have hcore : 2 * Real.sqrt x + 2 ≤ (7 / 400 : ℝ) * x := by
      let s : ℝ := Real.sqrt x
      have hs2 : s ^ 2 = x := by
        dsimp [s]
        exact Real.sq_sqrt hx0le
      have hs : 1000 ≤ s := by
        dsimp [s]
        exact hsqrt1000
      calc
        2 * s + 2 ≤ (7 / 400 : ℝ) * s ^ 2 := seven_fourhundred_sq_ge_two_s_add_two s hs
        _ = (7 / 400 : ℝ) * x := by rw [hs2]
    calc
      2 * Real.sqrt x + 2 ≤ (7 / 400 : ℝ) * x := hcore
      _ ≤ ((3 / 4) * Real.log 2 - 1 / 2) * x :=
        mul_le_mul_of_nonneg_right hδ hx0le
  calc
    Real.log (x + 1) + 2 * Real.sqrt x * Real.log x
        ≤ (2 * Real.sqrt x + 2) + x / 2 := add_le_add hB hA
    _ ≤ ((3 / 4) * Real.log 2 - 1 / 2) * x + x / 2 := by
      linarith
    _ = (3 / 4) * Real.log 2 * x := by ring

end Commons.Analysis.ExpLog