import Mathlib
import Submission.Work.Pert.StripChart
import Submission.Work.Pert.Strip.Defs
import Submission.Work.Pert.Strip.chartExp_strip
import Submission.Work.Pert.Strip.chart_hasDerivAt
import Submission.Work.Pert.Strip.norm_deriv_form
import Submission.Work.Pert.Strip.cayley_facts

/-!
# `Work.Pert.Strip.chart_facts`: the strip chart in action

`Work.Pert.stripChart h ζ = (E - 1)/(E + 1)` with `E = chartExp h ζ = exp (i π ζ/(2h))` is the
Cayley transform of the exponential chart of the vertical strip `|Re ζ| ≤ h > 0`.  Writing
`E = chartR h ζ · (cos (chartP h ζ) + i sin (chartP h ζ))` (see `Work.Pert.Strip.Defs`), the
Cayley transform gives the exact identity

    1 - ‖stripChart h ζ‖ ^ 2 = 4 * chartR h ζ * cos (chartP h ζ) / ‖E + 1‖ ^ 2              (†)

while `‖deriv (stripChart h) ζ‖ = 2 * chartK h * chartR h ζ / ‖E + 1‖ ^ 2`, so that

    1 - ‖stripChart h ζ‖ ^ 2 = cos (chartP h ζ) * ((4h/π) * ‖deriv (stripChart h) ζ‖).

Since `‖stripChart h ζ‖ ≤ ... ` reduces to `cos (chartP h ζ) ≥ 0`, which holds on the strip
`|Re ζ| ≤ h` because `chartP h ζ = π Re ζ/(2h) ∈ [-π/2, π/2]`, the chart maps the strip into the
closed unit disc and the Schwarz–Pick factor `(1 - ‖·‖²)/‖deriv‖ = (4h/π) cos (chartP h ζ)` is at
most `4h/π`: this is the content of `chart_facts`.
-/

namespace Work.Pert.Strip

noncomputable section

theorem chart_facts {h : ℝ} (hh : 0 < h) :
    DifferentiableOn ℂ (Work.Pert.stripChart h) {ζ : ℂ | |ζ.re| ≤ h} ∧
    (∀ ζ : ℂ, |ζ.re| ≤ h → ‖Work.Pert.stripChart h ζ‖ ≤ 1) ∧
    (∀ ζ : ℂ, |ζ.re| ≤ h →
      (1 - ‖Work.Pert.stripChart h ζ‖ ^ 2) ≤ (4 * h / Real.pi) * ‖deriv (Work.Pert.stripChart h) ζ‖) ∧
    (∀ ζ : ℂ, |ζ.re| ≤ h → deriv (Work.Pert.stripChart h) ζ ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the chart is holomorphic on the strip (the denominator `E + 1` does not vanish there)
    intro ζ hζ
    exact (chart_hasDerivAt hh hζ).differentiableAt.differentiableWithinAt
  · -- the chart maps the strip into the closed unit disc
    intro ζ hζ
    obtain ⟨hcos, hne⟩ := chartExp_strip hh hζ
    have hpos : 0 < chartR h ζ := Real.exp_pos _
    have hre : 0 ≤ (chartExp h ζ).re := by
      rw [chartExp_re h ζ]; exact mul_nonneg (le_of_lt hpos) hcos
    rw [stripChart_eq_cayley h ζ]
    exact (cayley_facts hne).2 hre
  · -- the Schwarz–Pick inequality, via the exact identity (†)
    intro ζ hζ
    obtain ⟨hcos, hne⟩ := chartExp_strip hh hζ
    have hpos : 0 < chartR h ζ := Real.exp_pos _
    have hre : (chartExp h ζ).re = chartR h ζ * Real.cos (chartP h ζ) := by
      rw [chartExp_re h ζ, chartR]
    have hderiv : deriv (Work.Pert.stripChart h) ζ
        = 2 * chartC h * chartExp h ζ / (chartExp h ζ + 1) ^ 2 :=
      (chart_hasDerivAt hh hζ).deriv
    have hd_norm : ‖deriv (Work.Pert.stripChart h) ζ‖
        = 2 * chartK h * chartR h ζ / ‖chartExp h ζ + 1‖ ^ 2 := by
      rw [hderiv]; exact norm_deriv_form hh ζ
    have hL : 1 - ‖Work.Pert.stripChart h ζ‖ ^ 2
        = 4 * (chartR h ζ * Real.cos (chartP h ζ)) / ‖chartExp h ζ + 1‖ ^ 2 := by
      rw [stripChart_eq_cayley h ζ, (cayley_facts hne).1, hre]
    have hk : (4 * h / Real.pi) * (2 * chartK h) = 4 := by
      rw [chartK]; field_simp
    have hR : (4 * h / Real.pi) * ‖deriv (Work.Pert.stripChart h) ζ‖
        = 4 * chartR h ζ / ‖chartExp h ζ + 1‖ ^ 2 := by
      rw [hd_norm]
      calc (4 * h / Real.pi) * (2 * chartK h * chartR h ζ / ‖chartExp h ζ + 1‖ ^ 2)
          = ((4 * h / Real.pi) * (2 * chartK h)) * chartR h ζ / ‖chartExp h ζ + 1‖ ^ 2 := by
            ring
        _ = 4 * chartR h ζ / ‖chartExp h ζ + 1‖ ^ 2 := by rw [hk]
    rw [hL, hR]
    apply div_le_div_of_nonneg_right
    · have := mul_le_mul_of_nonneg_left (Real.cos_le_one (chartP h ζ)) (le_of_lt hpos)
      linarith
    · positivity
  · -- the chart is a local biholomorphism: its derivative does not vanish on the strip
    intro ζ hζ
    obtain ⟨-, hne⟩ := chartExp_strip hh hζ
    rw [(chart_hasDerivAt hh hζ).deriv]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (chartC_ne_zero hh)) (chartExp_ne_zero h ζ))
      (pow_ne_zero 2 hne)

end

end Work.Pert.Strip
