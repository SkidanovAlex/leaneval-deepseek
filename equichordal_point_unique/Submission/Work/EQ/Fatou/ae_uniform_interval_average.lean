import Mathlib

namespace Work.EQ.Fatou

open MeasureTheory Set Metric Filter

open scoped Topology

theorem ae_uniform_interval_average (f : ℝ → ℂ) (hf : MeasureTheory.LocallyIntegrable f MeasureTheory.volume) :
    ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Set.Ioc (0:ℝ) δ,
      (MeasureTheory.volume (Set.Icc (θ - s) (θ + s))).toReal⁻¹ *
        ∫ y in Set.Icc (θ - s) (θ + s), ‖f y - f θ‖ < ε := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure ℝ) hf 1]
    with θ hθ
  intro ε hε
  have hmem : ∀ᶠ s : ℝ in 𝓝[>] (0:ℝ), θ ∈ closedBall θ (1 * s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [mem_closedBall, dist_self]
    exact mul_nonneg zero_le_one hs.le
  have h := hθ (fun _ : ℝ => θ) (fun s : ℝ => s) tendsto_id hmem
  have hlt : ∀ᶠ s : ℝ in 𝓝[>] (0:ℝ),
      ⨍ y in closedBall θ s, ‖f y - f θ‖ ∂volume < ε := (tendsto_order.1 h).2 ε hε
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hlt
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have heq : ⨍ y in closedBall θ s, ‖f y - f θ‖ ∂volume
      = (volume (Icc (θ - s) (θ + s))).toReal⁻¹ *
        ∫ y in Icc (θ - s) (θ + s), ‖f y - f θ‖ := by
    rw [Real.closedBall_eq_Icc, setAverage_eq, measureReal_def, smul_eq_mul]
  rw [← heq]
  exact hsub hs

end Work.EQ.Fatou
