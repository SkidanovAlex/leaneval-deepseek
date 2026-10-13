import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

/-- Continuity at `s₀ > 0` of the angular moment `s ↦ ∫ θ in Iθ, Ktheta θ * f s θ` of a function
`f` which is continuous on the open quadrant and locally bounded on a neighbourhood of `s₀`.

PROOF RECIPE.  Apply the existing engine
`Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound` with `G := fun z θ => f z θ`,
`φ := Work.Elliptic.Ktheta`, `z₀ := s₀`, `K := max A 0`; its conclusion is continuity of the
integral over `volume.restrict (Set.Ioo 0 (π/2))`, and
`MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc ..)` transfers it to `Iθ`.
The hypotheses: `ContinuousOn Ktheta Iθ` (it is `3*sin θ*cos θ ^ 2`); the eventual a.e. strong
measurability of `θ ↦ f z θ * Ktheta θ` from `Work.Spaces.aesm_slice_of_continuousOn_Qd` applied to
`(p : ℝ × ℝ) ↦ f p.1 p.2 * Ktheta p.2` (continuous on the open quadrant by `hcont`); the eventual
a.e. bound `‖f z θ‖ ≤ max A 0` from `hbd` on the open neighbourhood `Ioo (s₀/2) (2*s₀) ∋ s₀` of
`hs₀`; and the a.e. continuity of `z ↦ f z θ` at `s₀` from `hcont` at the interior point
`(s₀,θ)`, `θ ∈ (0,π/2)`. -/
theorem continuousAt_Qang_of_bounds {f : ℝ → ℝ → ℝ} {s₀ A : ℝ} (hs₀ : 0 < s₀)
    (hcont : ContinuousOn (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hbd : ∀ z θ : ℝ, z ∈ Set.Ioo (s₀ / 2) (2 * s₀) → 0 < θ → θ < Real.pi / 2 →
      |f z θ| ≤ A) :
    ContinuousAt (fun s => ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * f s θ) s₀ := by
  -- `s₀` has a neighbourhood on which the hypothesis `hbd` applies.
  have hU : Set.Ioo (s₀ / 2) (2 * s₀) ∈ nhds s₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hKtheta : Continuous Work.Elliptic.Ktheta := by
    unfold Work.Elliptic.Ktheta; fun_prop
  -- Eventual a.e. strong measurability of the slices.
  have hmeas : ∀ᶠ z in nhds s₀,
      MeasureTheory.AEStronglyMeasurable (fun θ => f z θ * Work.Elliptic.Ktheta θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    filter_upwards [hU] with z hz
    have hzpos : 0 < z := by linarith [hz.1]
    have h1 : ContinuousOn (fun θ : ℝ => f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => ⟨hzpos, hθ⟩)
    exact (h1.mul hKtheta.continuousOn).aestronglyMeasurable measurableSet_Ioo
  -- Eventual a.e. bound by `max A 0`.
  have hbound : ∀ᶠ z in nhds s₀,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))), ‖f z θ‖ ≤ max A 0 := by
    filter_upwards [hU] with z hz
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs]
    exact le_trans (hbd z θ hz hθ.1 hθ.2) (le_max_left _ _)
  -- A.e. continuity of the slices at `s₀`.
  have haecont : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ContinuousAt (fun z => f z θ) s₀ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hpt : (s₀, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hs₀, hθ⟩
    have hca : ContinuousAt (Function.uncurry f) (s₀, θ) :=
      hcont.continuousAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hpt)
    have hcomp := hca.comp (x := s₀) (continuousAt_id.prodMk continuousAt_const)
    simpa [Function.comp_def, Function.uncurry] using hcomp
  -- The engine, on the open interval `(0, π/2)`.
  have hmain := Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound
    (G := fun z θ => f z θ) (φ := Work.Elliptic.Ktheta) (z₀ := s₀) (K := max A 0)
    (le_max_right _ _) hKtheta.continuousOn hmeas hbound haecont
  -- Transfer from `(0, π/2)` to `Iθ = [0, π/2]`: the two differ by a null set.
  refine hmain.congr ?_
  filter_upwards with s
  simp only [Work.Spaces.Iθ]
  rw [MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)).symm]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => mul_comm _ _)

end Work.FTS_RegExport.RXT.Sys
