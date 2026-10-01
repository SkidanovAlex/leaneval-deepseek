import Mathlib
import Submission.Commons.Analysis.Real.log_one_add_lower
import Submission.Commons.Analysis.Real.log_one_add_upper

namespace Commons.Analysis.Real

/-- The purely algebraic core of the lower bound: with `w = 4 u (u+1)`,
`w/4 - 3 w^2/32 ≤ u - u^2/2` for `u ≥ 0`. -/
lemma arsinh_log_bounds_lower_arith {u : ℝ} (hu : 0 ≤ u) :
    u * (u + 1) - 3 * u ^ 2 * (u + 1) ^ 2 / 2 ≤ u - u ^ 2 / 2 := by
  have h : u - u ^ 2 / 2 - (u * (u + 1) - 3 * u ^ 2 * (u + 1) ^ 2 / 2)
      = 3 * u ^ 3 * (u + 2) / 2 := by ring
  have hnn : 0 ≤ 3 * u ^ 3 * (u + 2) / 2 := by
    have h3 : 0 ≤ u ^ 3 := pow_nonneg hu 3
    have h2 : 0 ≤ u + 2 := by linarith
    positivity
  have hd : 0 ≤ u - u ^ 2 / 2 - (u * (u + 1) - 3 * u ^ 2 * (u + 1) ^ 2 / 2) := by
    rw [h]; exact hnn
  linarith

theorem arsinh_log_bounds {y : ℝ} (hy : 1 ≤ y) :
    Real.log (2*y) + 1/(4*y^2) - 3/(32*y^4) ≤ Real.arsinh y ∧
      Real.arsinh y ≤ Real.log (2*y) + 1/(4*y^2) := by
  have hy_pos : 0 < y := by linarith
  have hyne : y ≠ 0 := ne_of_gt hy_pos
  have hy2_pos : 0 < y ^ 2 := by positivity
  have hw_nonneg : 0 ≤ 1 / y ^ 2 := by positivity
  have hw_le_one : 1 / y ^ 2 ≤ 1 := by
    rw [div_le_one₀ hy2_pos]
    nlinarith [hy]
  set s : ℝ := Real.sqrt (1 + 1 / y ^ 2) with hs_def
  have hs_sq : s ^ 2 = 1 + 1 / y ^ 2 := by
    rw [hs_def]; exact Real.sq_sqrt (by positivity)
  have hs_ge_one : 1 ≤ s := by
    rw [hs_def, ← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    linarith [hw_nonneg]
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_ge_one
  have hs_le_two : s ≤ 2 := by
    rw [hs_def, Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [hw_le_one]
  -- `√(1 + y²) = y * s`
  have hkey : Real.sqrt (1 + y ^ 2) = y * s := by
    have hsq : (y * s) ^ 2 = 1 + y ^ 2 := by
      rw [mul_pow, hs_sq]
      field_simp
      ring
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    exact hsq.symm
  -- Introduce `u := (s-1)/2 ≥ 0`.
  set u : ℝ := (s - 1) / 2 with hu_def
  have hu_nonneg : 0 ≤ u := by rw [hu_def]; linarith
  have hu_le_half : u ≤ 1 / 2 := by rw [hu_def]; linarith
  have h1u_pos : 0 < 1 + u := by linarith
  -- Decompose `arsinh y = log (2 y) + log (1 + u)`.
  have hs_eq : s = 2 * u + 1 := by rw [hu_def]; ring
  have hw_u : (1:ℝ) / y ^ 2 = 4 * u * (u + 1) := by
    have h1 : s ^ 2 - 1 = 1 / y ^ 2 := by linarith [hs_sq]
    have h2 : s ^ 2 - 1 = 4 * u * (u + 1) := by rw [hs_eq]; ring
    linarith
  have hA : Real.arsinh y = Real.log y + Real.log (1 + s) := by
    unfold Real.arsinh
    rw [hkey, show y + y * s = y * (1 + s) by ring]
    rw [Real.log_mul hyne (by positivity)]
  have h1s_eq : 1 + s = 2 * (1 + u) := by rw [hu_def]; ring
  have hB : Real.log (1 + s) = Real.log 2 + Real.log (1 + u) := by
    rw [h1s_eq, Real.log_mul (by norm_num) (ne_of_gt h1u_pos)]
  have hC : Real.log (2*y) = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hyne
  have harsinh_eq : Real.arsinh y = Real.log (2*y) + Real.log (1 + u) := by
    rw [hA, hB, hC]; ring
  -- Upper bound pieces.
  have h_e2 : (1:ℝ) / (4*y^2) = u * (u + 1) := by
    have h : (1:ℝ) / (4*y^2) = (1 / y^2) / 4 := by ring_nf
    rw [h, hw_u]; ring
  have hu_le_w : u ≤ 1 / (4*y^2) := by
    rw [h_e2]; nlinarith [sq_nonneg u]
  have hupper : Real.log (1 + u) ≤ 1 / (4*y^2) :=
    le_trans (log_one_add_upper hu_nonneg) hu_le_w
  -- Lower bound pieces.
  have h_e4 : (3:ℝ) / (32*y^4) = 3 * u ^ 2 * (u + 1) ^ 2 / 2 := by
    have h1 : (3:ℝ) / (32*y^4) = 3 * ((1:ℝ) / (32*y^4)) := by ring_nf
    have h2 : (1:ℝ) / (32*y^4) = ((1:ℝ) / y^4) / 32 := by ring_nf
    have h3 : (1:ℝ) / y^4 = ((1:ℝ) / y^2) ^ 2 := by ring_nf
    rw [h1, h2, h3, hw_u]; ring
  have h_lower_arith : (1:ℝ) / (4*y^2) - 3 / (32*y^4) ≤ u - u ^ 2 / 2 := by
    rw [h_e2, h_e4]
    exact arsinh_log_bounds_lower_arith hu_nonneg
  have h_lower_log : u - u ^ 2 / 2 ≤ Real.log (1 + u) :=
    log_one_add_lower (u₀ := 1/2) (by norm_num) hu_nonneg hu_le_half
  constructor
  · rw [harsinh_eq]; linarith
  · rw [harsinh_eq]; linarith

end Commons.Analysis.Real
