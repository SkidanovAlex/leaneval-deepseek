import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

theorem continuousAt_integral_Itheta_of_bound {G : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {z₀ K : ℝ}
    (hK : 0 ≤ K) (hφ : ContinuousOn φ Work.Spaces.Iθ)
    (hG_meas : ∀ᶠ z in nhds z₀,
      MeasureTheory.AEStronglyMeasurable (fun θ => G z θ * φ θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hbound : ∀ᶠ z in nhds z₀,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))), ‖G z θ‖ ≤ K)
    (hcont : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ContinuousAt (fun z => G z θ) z₀) :
    ContinuousAt (fun z => ∫ θ, G z θ * φ θ
      ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) z₀ := by
  -- The interval `(0, π/2)` is of finite measure, so constants are integrable.
  have hfin : MeasureTheory.volume (Set.Ioo (0 : ℝ) (Real.pi / 2)) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono Set.Ioo_subset_Icc_self)
      isCompact_Icc.measure_lt_top
  have hfinI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hfin⟩
  -- `φ` is bounded on the compact interval `Iθ`.
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  have hφae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      ‖φ θ‖ ≤ M := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact hM θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- The dominating function, and the a.e. bound by it.
  have hbound' : ∀ᶠ z in nhds z₀,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
        ‖G z θ * φ θ‖ ≤ K * M := by
    filter_upwards [hbound] with z hz
    filter_upwards [hz, hφae] with θ h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) hK
  -- The a.e. convergence of the slices.
  have hcont' : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      ContinuousAt (fun z => G z θ * φ θ) z₀ := by
    filter_upwards [hcont] with θ hθ
    exact hθ.tendsto.mul_const (φ θ)
  have hbint : MeasureTheory.Integrable (fun _ : ℝ => K * M)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    MeasureTheory.integrable_const_iff.2 (Or.inr hfinI)
  exact MeasureTheory.continuousAt_of_dominated (F := fun z θ => G z θ * φ θ)
    (x₀ := z₀) (bound := fun _ => K * M) hG_meas hbound' hbint hcont'

end Work.FTS_RegExport.RXT
