import Mathlib

namespace Work.TMC16Core.Assembly

open Filter

theorem rate_log_shift (Kc : ℝ) : Filter.Tendsto (fun qn : ℝ => 2 * (Kc + 20 * Real.log (qn + 2)) / qn) Filter.atTop (nhds 0) := by
  -- `qn + 2 → atTop`
  have hq2 : Filter.Tendsto (fun qn : ℝ => qn + 2) Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right Filter.atTop 2 tendsto_id
  -- `log (qn + 2) / qn → 0`, from `log x / (x - 2) → 0` at `x = qn + 2`.
  have hlog : Filter.Tendsto (fun qn : ℝ => Real.log (qn + 2) / qn) Filter.atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (-2) 1 one_ne_zero).comp hq2
    simpa [Function.comp_def] using h
  -- the constant part `2 * Kc / qn → 0`
  have hconst : Filter.Tendsto (fun qn : ℝ => 2 * Kc / qn) Filter.atTop (nhds 0) :=
    (tendsto_const_nhds (x := 2 * Kc)).div_atTop tendsto_id
  have hsum : Filter.Tendsto (fun qn : ℝ => 2 * Kc / qn + 40 * (Real.log (qn + 2) / qn))
      Filter.atTop (nhds 0) := by
    have h := hconst.add (hlog.const_mul (40 : ℝ))
    simpa using h
  have heq : (fun qn : ℝ => 2 * (Kc + 20 * Real.log (qn + 2)) / qn)
      = (fun qn : ℝ => 2 * Kc / qn + 40 * (Real.log (qn + 2) / qn)) := by
    funext qn
    by_cases h : qn = 0
    · simp [h]
    · field_simp
      ring
  rw [heq]
  exact hsum

end Work.TMC16Core.Assembly
