import Mathlib

namespace Work.TMC16Core.Assembly

open Filter
open scoped Topology

theorem uni_res_rate {b₀ cθ L : ℝ} (hb₀ : 0 < b₀) (hcθ : 0 < cθ) (hLb : 16 * b₀ / 9 < L) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ qn : ℝ, Q ≤ qn →
      b₀ / 2 + b₀ / (4 * qn - 2) + 2 * Real.log (1 / cθ) / qn
        + 200 * Real.log qn / qn + 200 / qn ≤ 9 * L / 32 - (9 * L / 32 - b₀ / 2) / 2 := by
  have hden : Tendsto (fun qn : ℝ => 4 * qn - 2) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop ((b + 2) / 4)] with qn hqn
    linarith
  have h1 : Tendsto (fun qn : ℝ => b₀ / (4 * qn - 2)) atTop (𝓝 0) :=
    hden.const_div_atTop b₀
  have h2 : Tendsto (fun qn : ℝ => 2 * Real.log (1 / cθ) / qn) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := 2 * Real.log (1 / cθ))).div_atTop tendsto_id
  have hlog : Tendsto (fun qn : ℝ => Real.log qn / qn) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h3 : Tendsto (fun qn : ℝ => 200 * Real.log qn / qn) atTop (𝓝 0) := by
    have := hlog.const_mul (200 : ℝ)
    simpa [mul_div_assoc] using this
  have h4 : Tendsto (fun qn : ℝ => 200 / qn) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (200 : ℝ))).div_atTop tendsto_id
  have hc : Tendsto (fun _ : ℝ => b₀ / 2) atTop (𝓝 (b₀ / 2)) := tendsto_const_nhds
  have htend : Tendsto (fun qn : ℝ => b₀ / 2 + b₀ / (4 * qn - 2) + 2 * Real.log (1 / cθ) / qn
        + 200 * Real.log qn / qn + 200 / qn) atTop (𝓝 (b₀ / 2)) := by
    have := (((hc.add h1).add h2).add h3).add h4
    simpa using this
  have hlt : b₀ / 2 < 9 * L / 32 - (9 * L / 32 - b₀ / 2) / 2 := by linarith [hLb]
  have hev : ∀ᶠ qn : ℝ in atTop,
      b₀ / 2 + b₀ / (4 * qn - 2) + 2 * Real.log (1 / cθ) / qn
        + 200 * Real.log qn / qn + 200 / qn < 9 * L / 32 - (9 * L / 32 - b₀ / 2) / 2 :=
    (tendsto_order.1 htend).2 _ hlt
  rw [eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  refine ⟨max a 1, lt_of_lt_of_le zero_lt_one (le_max_right a 1), ?_⟩
  intro qn hqn
  exact le_of_lt (ha qn (le_trans (le_max_left a 1) hqn))

end Work.TMC16Core.Assembly
