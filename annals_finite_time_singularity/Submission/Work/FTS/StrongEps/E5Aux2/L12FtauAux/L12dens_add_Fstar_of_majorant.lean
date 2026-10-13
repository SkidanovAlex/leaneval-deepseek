import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.Stability.L12Add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2.L12FtauAux

/-- **The angular slice of a majorised continuous profile is integrable on `Iθ`.**

If `h` is continuous on the open quadrant `Q0 = (0,∞) × (0,π/2)` and is dominated
pointwise by `Maj σ` on every angular interval `(0,π/2)`, then for every `σ > 0` the
integrand `θ ↦ K θ · h σ θ / σ` of the `L₁₂`-density is integrable on the compact
interval `Iθ = [0,π/2]`: it is continuous on the co-null open interval `(0,π/2)` (hence
a.e.-strongly measurable on `Iθ`) and bounded there by `3·Maj σ / σ` (using `|K| ≤ 3`),
and `Iθ` has finite Lebesgue measure. -/
private lemma integrableOn_slice_of_majorant {h : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ}
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h σ θ| ≤ Maj σ)
    {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * h σ θ / σ) Work.Spaces.Iθ := by
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    unfold Work.Spaces.K; fun_prop
  have hsl : ContinuousOn (fun θ => h σ θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hh.comp (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => ⟨hσ, hθ⟩)
  have hcont : ContinuousOn (fun θ => Work.Spaces.K θ * h σ θ / σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hK.mul hsl).div_const σ
  have hmeas1 : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * h σ θ / σ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hIoo : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := Real.pi / 2))
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * h σ θ / σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [← hIoo]; exact hmeas1
  have hbdd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * h σ θ / σ‖ ≤ 3 * Maj σ / σ := by
    rw [← hIoo]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    have hKb : |Work.Spaces.K θ| ≤ 3 := by
      unfold Work.Spaces.K
      rw [show |3 * Real.sin θ * Real.cos θ ^ 2| = 3 * |Real.sin θ| * |Real.cos θ| ^ 2 by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_pow]]
      nlinarith [Real.abs_sin_le_one θ, Real.abs_cos_le_one θ,
        abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
    have hhb : |h σ θ| ≤ Maj σ := hbd σ (Set.mem_Ioi.mpr hσ) θ hθ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hσ, abs_mul]
    have h1 : |Work.Spaces.K θ| * |h σ θ| ≤ 3 * Maj σ := by
      nlinarith [abs_nonneg (h σ θ)]
    rw [div_le_div_iff_of_pos_right hσ]
    exact h1
  exact MeasureTheory.IntegrableOn.of_bound (s := Work.Spaces.Iθ)
    (by rw [Work.Spaces.Iθ]; exact measure_Icc_lt_top) hmeas _ hbdd

theorem L12dens_add_Fstar_of_majorant {α : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ}
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h σ θ| ≤ Maj σ)
    {σ : ℝ} (hσ : 0 < σ) :
    Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.Fstar α z θ + h z θ) σ
      = Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) σ
        + Work.FM.L12dens Work.Spaces.K h σ :=
  Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
    (Work.Stability.integrableOn_slice_Fstar α hα σ)
    (integrableOn_slice_of_majorant hh hbd hσ)

end Work.FTS.StrongEps.E5Aux2.L12FtauAux
