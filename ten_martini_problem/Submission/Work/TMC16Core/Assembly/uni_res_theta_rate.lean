import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.rate_b0_div
import Submission.Work.TMC16Core.Assembly.rate_log_shift

namespace Work.TMC16Core.Assembly

/-- All four slowly varying tail terms that occur in `uni_res_theta_rate` vanish
as `qn → ∞`:

`b₀ / (4 qn - 2)`, `2 (Kc + 20 log (qn + 2)) / qn`, `200 log qn / qn`, `200 / qn`. -/
theorem rate_tail_tendsto (b₀ Kc : ℝ) :
    Filter.Tendsto (fun qn : ℝ =>
        b₀ / (4 * qn - 2) + 2 * (Kc + 20 * Real.log (qn + 2)) / qn
          + 200 * Real.log qn / qn + 200 / qn) Filter.atTop (nhds 0) := by
  -- `200 log qn / qn → 0` (the `Real.isLittleO_log_id_atTop` asymptotics)
  have hlog : Filter.Tendsto (fun qn : ℝ => Real.log qn / qn) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h4 : Filter.Tendsto (fun qn : ℝ => 200 * Real.log qn / qn) Filter.atTop (nhds 0) := by
    have := Filter.Tendsto.const_mul (200 : ℝ) hlog
    simpa [mul_div_assoc] using this
  -- `200 / qn → 0`
  have h5 : Filter.Tendsto (fun qn : ℝ => (200 : ℝ) / qn) Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop Filter.tendsto_id 200
  have hsum := (((rate_b0_div b₀).add (rate_log_shift Kc)).add h4).add h5
  simpa using hsum

/-- Rate estimate for the uniform resonance section: for all sufficiently large `qn`
the slowly varying tail terms are dominated by the gap between the two sides of the
Ten Martini separation inequality.  The hypothesis `16 * b₀ / 9 < L` is exactly what
makes that gap strictly positive. -/
theorem uni_res_theta_rate {b₀ L Kc : ℝ} (hb₀ : 0 < b₀) (hLb : 16 * b₀ / 9 < L) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ qn : ℝ, Q ≤ qn →
      b₀ / 2 + b₀ / (4 * qn - 2) + 2 * (Kc + 20 * Real.log (qn + 2)) / qn
        + 200 * Real.log qn / qn + 200 / qn
        ≤ 9 * L / 32 - (9 * L / 32 - b₀ / 2) / 2 := by
  -- the right-hand side exceeds `b₀ / 2` by a positive gap
  have hgap : b₀ / 2 < 9 * L / 32 - (9 * L / 32 - b₀ / 2) / 2 := by linarith [hb₀]
  -- the left-hand side tends to `b₀ / 2`
  have hsum : Filter.Tendsto (fun qn : ℝ =>
      b₀ / 2 + b₀ / (4 * qn - 2) + 2 * (Kc + 20 * Real.log (qn + 2)) / qn
        + 200 * Real.log qn / qn + 200 / qn) Filter.atTop (nhds (b₀ / 2)) := by
    have hconst : Filter.Tendsto (fun _ : ℝ => b₀ / 2) Filter.atTop (nhds (b₀ / 2)) :=
      tendsto_const_nhds
    have h := hconst.add (rate_tail_tendsto b₀ Kc)
    simpa only [add_assoc, add_zero] using h
  -- hence it is eventually below the right-hand side
  have hev : ∀ᶠ qn in Filter.atTop,
      b₀ / 2 + b₀ / (4 * qn - 2) + 2 * (Kc + 20 * Real.log (qn + 2)) / qn
        + 200 * Real.log qn / qn + 200 / qn
        ≤ 9 * L / 32 - (9 * L / 32 - b₀ / 2) / 2 := by
    filter_upwards [Filter.Tendsto.eventually_lt_const hgap hsum] with qn hqn
    exact le_of_lt hqn
  rw [Filter.eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  exact ⟨max a 1, lt_of_lt_of_le one_pos (le_max_right a 1),
    fun qn hqn => ha qn (le_trans (le_max_left a 1) hqn)⟩

end Work.TMC16Core.Assembly
