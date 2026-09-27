import Mathlib

namespace Work.EQ.FanTri

open scoped NNReal ENNReal

/-- A function analytic at a point of a complex normed space is locally Lipschitz there, with an
explicit ball: there are `ρ > 0` and `C ≥ 0` such that `‖f x - f y‖ ≤ C * ‖x - y‖` for all `x`,
`y` with `‖x - z‖ ≤ ρ` and `‖y - z‖ ≤ ρ`.

Route: `AnalyticAt ℂ f z` unpacks as `∃ p r, HasFPowerSeriesOnBall f p z r` with `0 < r`
(`r : ℝ≥0∞`); pick `r' : ℝ≥0` with `0 < r' < r` (`ENNReal.lt_iff_exists_nnreal_btwn`).  Mathlib's
`HasFPowerSeriesOnBall.image_sub_sub_deriv_le` (`.lake/packages/mathlib/Mathlib/Analysis/Analytic/
Basic.lean:870`) then gives, for `x, y ∈ Metric.eball z r'` and some `C`, the Taylor remainder
bound `‖f x - f y - (p 1) (x - y)‖ ≤ C * max ‖x - z‖ ‖y - z‖ * ‖x - y‖`.  Taking
`ρ = (r' : ℝ) / 2` (so the closed `ρ`-ball stays inside `Metric.eball z r'`, using
`Metric.mem_eball` and `Metric.edist_lt_coe`), `max ‖x-z‖ ‖y-z‖ ≤ ρ`, and
`‖(p 1) (x - y)‖ ≤ ‖p 1‖ * ‖x - y‖` (`ContinuousMultilinearMap.le_opNorm` with the single
coordinate), giving `C₀ = ‖p 1‖ + |C| * ρ ≥ 0`. -/
theorem analytic_lipschitz_ball {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {z : E} (hf : AnalyticAt ℂ f z) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ x y : E,
      ‖x - z‖ ≤ ρ → ‖y - z‖ ≤ ρ → ‖f x - f y‖ ≤ C * ‖x - y‖ := by
  obtain ⟨p, r, hf⟩ := hf
  obtain ⟨r', hr'pos, hr'lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos
  have hr'pos' : (0 : ℝ≥0) < r' := ENNReal.coe_pos.mp hr'pos
  have hrR : (0 : ℝ) < (r' : ℝ) := by exact_mod_cast hr'pos'
  obtain ⟨C, hC⟩ := hf.image_sub_sub_deriv_le hr'lt
  refine ⟨(r' : ℝ) / 2, ‖p 1‖ + |C| * ((r' : ℝ) / 2), ?_, ?_, ?_⟩
  · linarith
  · positivity
  · intro x y hx hy
    have hxmem : x ∈ Metric.eball z (r' : ℝ≥0∞) := by
      rw [Metric.mem_eball, edist_lt_coe, ← NNReal.coe_lt_coe]
      rw [coe_nndist, dist_eq_norm]
      linarith
    have hymem : y ∈ Metric.eball z (r' : ℝ≥0∞) := by
      rw [Metric.mem_eball, edist_lt_coe, ← NNReal.coe_lt_coe]
      rw [coe_nndist, dist_eq_norm]
      linarith
    have hop : ‖(p 1) (fun _ : Fin 1 => x - y)‖ ≤ ‖p 1‖ * ‖x - y‖ := by
      have := ContinuousMultilinearMap.le_opNorm (p 1) (fun _ : Fin 1 => x - y)
      simpa using this
    have hmax : max ‖x - z‖ ‖y - z‖ ≤ (r' : ℝ) / 2 := max_le hx hy
    have h1 : ‖f x - f y - (p 1) (fun _ : Fin 1 => x - y)‖ ≤
        |C| * ((r' : ℝ) / 2 * ‖x - y‖) := by
      have hmnn : (0 : ℝ) ≤ max ‖x - z‖ ‖y - z‖ := by positivity
      have hnn : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
      calc ‖f x - f y - (p 1) (fun _ : Fin 1 => x - y)‖
          ≤ C * max ‖x - z‖ ‖y - z‖ * ‖x - y‖ := hC x hxmem y hymem
        _ = C * (max ‖x - z‖ ‖y - z‖ * ‖x - y‖) := by ring
        _ ≤ |C| * (max ‖x - z‖ ‖y - z‖ * ‖x - y‖) :=
              mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg hmnn hnn)
        _ ≤ |C| * ((r' : ℝ) / 2 * ‖x - y‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmax hnn) (abs_nonneg C)
    have hkey : ‖f x - f y‖ ≤
        ‖f x - f y - (p 1) (fun _ : Fin 1 => x - y)‖ +
          ‖(p 1) (fun _ : Fin 1 => x - y)‖ := by
      have := norm_add_le (f x - f y - (p 1) (fun _ : Fin 1 => x - y))
        ((p 1) (fun _ : Fin 1 => x - y))
      simpa [sub_add_cancel] using this
    calc ‖f x - f y‖
        ≤ ‖f x - f y - (p 1) (fun _ : Fin 1 => x - y)‖ +
            ‖(p 1) (fun _ : Fin 1 => x - y)‖ := hkey
      _ ≤ |C| * ((r' : ℝ) / 2 * ‖x - y‖) + ‖p 1‖ * ‖x - y‖ := add_le_add h1 hop
      _ = (‖p 1‖ + |C| * ((r' : ℝ) / 2)) * ‖x - y‖ := by ring

end Work.EQ.FanTri
