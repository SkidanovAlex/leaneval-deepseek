import Mathlib

namespace Work.EQ.Fatou

open MeasureTheory Filter
open scoped ENNReal

/-- Lyapunov / Cauchy–Schwarz inequality on a finite measure space: the `L¹` norm of an
element of `L²` is controlled by its `L²` norm, with constant `(μ univ)^{1/2}`,

`∫ x, ‖G x‖ ∂μ ≤ ‖G‖_{L²} · (μ univ)^{1/2}`.

Formally this is the comparison of `eLpNorm`s for the exponents `1 ≤ 2` combined with
`∫ ‖G x‖ ∂μ = (eLpNorm G 1 μ).toReal`. -/
theorem integral_coeFn_norm_le {μ : Measure ℝ} [IsFiniteMeasure μ] (G : Lp ℂ 2 μ) :
    ∫ x, ‖(G : ℝ → ℂ) x‖ ∂μ ≤ ‖G‖ * (μ Set.univ).toReal ^ (1/2 : ℝ) := by
  have hsm : AEStronglyMeasurable (G : ℝ → ℂ) μ := Lp.aestronglyMeasurable G
  rw [MeasureTheory.integral_norm_eq_lintegral_enorm hsm,
    ← MeasureTheory.eLpNorm_one_eq_lintegral_enorm hsm]
  have hle := MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ)
      (f := (G : ℝ → ℂ)) (p := (1:ENNReal)) (q := (2:ENNReal)) (by norm_num) hsm
  have hexp : (1:ℝ) / (1:ENNReal).toReal - 1 / (2:ENNReal).toReal = 1/2 := by norm_num
  rw [hexp] at hle
  have hb : eLpNorm (G : ℝ → ℂ) 2 μ * μ Set.univ ^ (1/2:ℝ) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact Lp.eLpNorm_ne_top G
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
  calc (eLpNorm (G : ℝ → ℂ) 1 μ).toReal
      ≤ (eLpNorm (G : ℝ → ℂ) 2 μ * μ Set.univ ^ (1/2:ℝ)).toReal := ENNReal.toReal_mono hb hle
    _ = (eLpNorm (G : ℝ → ℂ) 2 μ).toReal * (μ Set.univ ^ (1/2:ℝ)).toReal := ENNReal.toReal_mul
    _ = ‖G‖ * (μ Set.univ).toReal ^ (1/2:ℝ) := by rw [Lp.norm_def, ENNReal.toReal_rpow]

theorem tendsto_integral_norm_of_tendsto_Lp {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasure μ]
    {u : ℕ → ℝ → ℂ} (hMem : ∀ n, MeasureTheory.MemLp (u n) 2 μ)
    {F : MeasureTheory.Lp ℂ 2 μ}
    (h : Filter.Tendsto (fun n => (hMem n).toLp (u n)) Filter.atTop (nhds F)) :
    Filter.Tendsto (fun n => ∫ x, ‖u n x - (F : ℝ → ℂ) x‖ ∂μ) Filter.atTop (nhds 0) := by
  -- `‖(hMem n).toLp (u n) - F‖ → 0` from the `L²` convergence of `h`.
  have hnorm : Tendsto (fun n => ‖(hMem n).toLp (u n) - F‖) atTop (nhds 0) := by
    have h0 : Tendsto (fun n => (hMem n).toLp (u n) - F) atTop (nhds (0 : Lp ℂ 2 μ)) := by
      simpa using h.sub_const F
    simpa using h0.norm
  -- Pointwise-in-`n` bound of the `L¹` integral of the difference by the `L²` norm.
  have hbound : ∀ n, ∫ x, ‖u n x - (F : ℝ → ℂ) x‖ ∂μ
      ≤ ‖(hMem n).toLp (u n) - F‖ * (μ Set.univ).toReal ^ (1/2 : ℝ) := by
    intro n
    have hae : (fun x => ‖((hMem n).toLp (u n) - F : Lp ℂ 2 μ) x‖)
        =ᵐ[μ] (fun x => ‖u n x - (F : ℝ → ℂ) x‖) := by
      filter_upwards [Lp.coeFn_sub ((hMem n).toLp (u n)) F, MemLp.coeFn_toLp (hMem n)]
        with x h1 h2
      simp only [Pi.sub_apply] at h1 ⊢
      rw [h1, h2]
    rw [← integral_congr_ae hae]
    exact integral_coeFn_norm_le _
  have htend : Tendsto
      (fun n => ‖(hMem n).toLp (u n) - F‖ * (μ Set.univ).toReal ^ (1/2 : ℝ)) atTop (nhds 0) := by
    have := hnorm.mul_const ((μ Set.univ).toReal ^ (1/2 : ℝ))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ))
    (h := fun n => ‖(hMem n).toLp (u n) - F‖ * (μ Set.univ).toReal ^ (1/2 : ℝ))
    tendsto_const_nhds htend (fun n => integral_nonneg (fun x => norm_nonneg _)) hbound

end Work.EQ.Fatou
