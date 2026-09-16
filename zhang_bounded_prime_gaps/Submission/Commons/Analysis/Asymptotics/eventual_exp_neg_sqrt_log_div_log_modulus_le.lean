import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold

namespace Commons.Analysis.Asymptotics

/-- For `A > 0` and `c > 0`, eventually for real `x` and every natural `N` with
`N ≤ (log x)^A`, one has
`exp (-(c/2) * sqrt (log x / log (N+2))) ≤ 1 / (log x)^(2A)`.

Indeed `log (N + 2) ≤ 2 A log (log x)` for large `x`, so the exponent is at most
`-(c/2) * sqrt (log x / (2 A log log x))`, which dominates `2 A log log x`
precisely because `(log L)^3 ≤ L` for large `L`. -/
theorem eventual_exp_neg_sqrt_log_div_log_modulus_le (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∃ x₁ : ℝ, 1 ≤ x₁ ∧ ∀ x : ℝ, x₁ ≤ x → ∀ N : ℕ,
      (N : ℝ) ≤ (Real.log x) ^ A →
      Real.exp (-(c / 2) * Real.sqrt (Real.log x / Real.log ((N : ℝ) + 2)))
        ≤ 1 / (Real.log x) ^ (2 * A) := by
  set K : ℝ := 32 * A ^ 3 / c ^ 2 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  -- Threshold beyond which `K * (log L)^3 ≤ L`.
  obtain ⟨X0, hX0ge1, hX0⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := K) hKpos.le
      (n := 3) (r := 1) (by norm_num)
  -- Overall threshold on `log x`.
  set L0 : ℝ := max (max X0 2) (Real.exp (Real.log 3 / A)) with hL0def
  have hL0nonneg : 0 ≤ L0 := by
    rw [hL0def]
    exact le_trans (le_trans (by linarith : (0 : ℝ) ≤ X0) (le_max_left X0 2)) (le_max_left _ _)
  refine ⟨Real.exp L0, Real.one_le_exp hL0nonneg, ?_⟩
  intro x hx N hN
  set L : ℝ := Real.log x with hLdef
  have hxpos : 0 < x := by
    have : (0 : ℝ) < Real.exp L0 := Real.exp_pos L0
    linarith
  have hL0le : L0 ≤ L := by
    have h := Real.log_le_log (Real.exp_pos L0) hx
    rw [Real.log_exp] at h
    rw [← hLdef] at h
    exact h
  have hLX0 : X0 ≤ L := le_trans (le_trans (le_max_left X0 2) (le_max_left _ _)) hL0le
  have hL2 : 2 ≤ L := le_trans (le_trans (le_max_right X0 2) (le_max_left _ _)) hL0le
  have hLexp : Real.exp (Real.log 3 / A) ≤ L := le_trans (le_max_right _ _) hL0le
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlogLpos : 0 < Real.log L := Real.log_pos (by linarith : (1 : ℝ) < L)
  have hLA1 : 1 ≤ L ^ A := Real.one_le_rpow hL1 hA.le
  have hMpos : 0 < Real.log ((N : ℝ) + 2) := by
    apply Real.log_pos
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  -- `N + 2 ≤ 3 * L^A`, hence `log (N+2) ≤ 2 A log L`.
  have hN2 : (N : ℝ) + 2 ≤ 3 * L ^ A := by nlinarith [hN, hLA1]
  have hMle : Real.log ((N : ℝ) + 2) ≤ 2 * A * Real.log L := by
    have hlog3 : Real.log 3 ≤ A * Real.log L := by
      have hle : Real.log 3 / A ≤ Real.log L := by
        have h := Real.log_le_log (Real.exp_pos (Real.log 3 / A)) hLexp
        rwa [Real.log_exp] at h
      have hm := mul_le_mul_of_nonneg_left hle hA.le
      rwa [mul_div_cancel₀ (Real.log 3) (ne_of_gt hA)] at hm
    calc Real.log ((N : ℝ) + 2) ≤ Real.log (3 * L ^ A) :=
          Real.log_le_log (by positivity) hN2
      _ = Real.log 3 + Real.log (L ^ A) :=
          Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hLpos A))
      _ = Real.log 3 + A * Real.log L := by rw [Real.log_rpow hLpos]
      _ ≤ 2 * A * Real.log L := by linarith
  -- `log x / log (N+2) ≥ log x / (2 A log log x)`.
  have hfrac : L / (2 * A * Real.log L) ≤ L / Real.log ((N : ℝ) + 2) :=
    div_le_div_of_nonneg_left hLpos.le hMpos hMle
  have hsqrt : Real.sqrt (L / (2 * A * Real.log L))
      ≤ Real.sqrt (L / Real.log ((N : ℝ) + 2)) := Real.sqrt_le_sqrt hfrac
  -- Core algebraic inequality.
  have hdenpos : 0 < 2 * A * Real.log L := by nlinarith [hA, hlogLpos]
  have hK' : K * (Real.log L) ^ 3 ≤ L := by
    have h := hX0 L hLX0
    rwa [Real.rpow_one] at h
  have hMsq : (2 * A * Real.log L) ^ 2 ≤ ((c / 2) * Real.sqrt (L / (2 * A * Real.log L))) ^ 2 := by
    have hz : 0 ≤ L / (2 * A * Real.log L) := div_nonneg hLpos.le hdenpos.le
    have hsqrt_sq : ((c / 2) * Real.sqrt (L / (2 * A * Real.log L))) ^ 2
        = (c / 2) ^ 2 * (L / (2 * A * Real.log L)) := by
      rw [mul_pow, Real.sq_sqrt hz]
    rw [hsqrt_sq]
    have h2 : K * (Real.log L) ^ 3 / (2 * A * Real.log L)
        ≤ L / (2 * A * Real.log L) := div_le_div_of_nonneg_right hK' hdenpos.le
    have h3 : (c / 2) ^ 2 * (K * (Real.log L) ^ 3 / (2 * A * Real.log L))
        ≤ (c / 2) ^ 2 * (L / (2 * A * Real.log L)) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have h4 : (c / 2) ^ 2 * (K * (Real.log L) ^ 3 / (2 * A * Real.log L))
        = (2 * A * Real.log L) ^ 2 := by
      rw [hKdef]
      field_simp
      ring
    rw [← h4]
    exact h3
  have hkey' : 2 * A * Real.log L ≤ (c / 2) * Real.sqrt (L / (2 * A * Real.log L)) := by
    have h := sq_le_sq.mp hMsq
    rw [abs_of_nonneg (by nlinarith [hA, hlogLpos]),
        abs_of_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c / 2) (Real.sqrt_nonneg _))] at h
    exact h
  have hfull : 2 * A * Real.log L ≤ (c / 2) * Real.sqrt (L / Real.log ((N : ℝ) + 2)) :=
    le_trans hkey' (mul_le_mul_of_nonneg_left hsqrt (by linarith : (0 : ℝ) ≤ c / 2))
  -- Take exponentials.
  have hexp_le : Real.exp (-(c / 2) * Real.sqrt (L / Real.log ((N : ℝ) + 2)))
      ≤ Real.exp (-(2 * A * Real.log L)) := by
    rw [Real.exp_le_exp]
    linarith
  have htarget : Real.exp (-(2 * A * Real.log L)) = 1 / L ^ (2 * A) := by
    rw [one_div, ← Real.rpow_neg hLpos.le (2 * A), Real.rpow_def_of_pos hLpos (-(2 * A))]
    congr 1
    ring
  rw [← htarget]
  exact hexp_le

end Commons.Analysis.Asymptotics