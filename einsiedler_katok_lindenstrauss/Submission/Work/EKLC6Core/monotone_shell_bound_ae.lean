import Mathlib
import Submission.Work.EKLC6Core.Basic

namespace Work.EKLC6Core

open scoped Topology
open Filter

/-- For a monotone function `F : ℝ → ℝ`, at almost every point `r` the symmetric increments
`F (r + h) - F (r - h)` are bounded above by a constant multiple of `h`, for all sufficiently
small `h > 0`.

The proof uses that a monotone function is Lebesgue-almost everywhere differentiable
(`Monotone.ae_hasDerivAt`). At a differentiability point `r` the symmetric difference quotient
`(F (r + h) - F (r - h)) / h` tends to twice the derivative, hence is eventually bounded above
by a constant. -/
theorem monotone_shell_bound_ae (F : ℝ → ℝ) (hF : Monotone F) :
    ∀ᵐ r ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ∃ c h₀ : ℝ, 0 < c ∧ 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ → F (r + h) - F (r - h) ≤ c * h := by
  -- Almost every point is a differentiability point of `F`, with derivative `d`.
  filter_upwards [hF.ae_hasDerivAt] with r hr
  set d : ℝ := (hF.stieltjesFunction.measure.rnDeriv MeasureTheory.volume r).toReal
  -- Derivative of `h ↦ F (r + h)` at `0` is `d`.
  have h1 : HasDerivAt (fun h : ℝ => F (r + h)) d 0 := by
    have hr0 : HasDerivAt F d (r + 0) := by rw [add_zero]; exact hr
    exact hr0.comp_const_add r 0
  -- Derivative of `h ↦ F (r - h)` at `0` is `-d`.
  have h2 : HasDerivAt (fun h : ℝ => F (r - h)) (-d) 0 := by
    have hr0 : HasDerivAt F d (r - 0) := by rw [sub_zero]; exact hr
    exact hr0.comp_const_sub r 0
  -- Derivative of the symmetric increment at `0`.
  have hH := h1.sub h2
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hH).mono_left (nhdsGT_le_nhdsNE (0:ℝ))
  -- Hence the symmetric difference quotient tends to `d - (-d)`.
  have htend : Filter.Tendsto (fun h : ℝ => (F (r + h) - F (r - h)) / h) (𝓝[>] (0:ℝ))
      (𝓝 (d - (-d))) := by
    refine Filter.Tendsto.congr' ?_ hslope
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [slope_fun_def_field]
    simp [Pi.sub_apply]
  -- So eventually the symmetric increment is bounded by `(d - (-d) + 1) * h`.
  have hev : ∀ᶠ h in 𝓝[>] (0:ℝ), F (r + h) - F (r - h) < (d - (-d) + 1) * h := by
    have hmem : Set.Iio (d - (-d) + 1) ∈ 𝓝 (d - (-d)) := Iio_mem_nhds (by linarith)
    filter_upwards [htend.eventually hmem, self_mem_nhdsWithin] with h hh hpos
    rw [div_lt_iff₀ hpos] at hh
    exact hh
  -- Extract a positive radius from the "eventually at `0⁺`" statement.
  obtain ⟨h₀, hh₀pos, hh₀⟩ := (nhdsGT_basis (0:ℝ)).mem_iff.mp hev
  refine ⟨|d - (-d)| + 1, h₀, ?_, hh₀pos, ?_⟩
  · positivity
  · intro h hpos hlt
    have hh := hh₀ ⟨hpos, hlt⟩
    calc F (r + h) - F (r - h) ≤ (d - (-d) + 1) * h := le_of_lt hh
      _ ≤ (|d - (-d)| + 1) * h := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hpos)
          linarith [le_abs_self (d - (-d))]

end Work.EKLC6Core
