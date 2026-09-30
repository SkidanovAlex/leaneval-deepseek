import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter
open scoped Topology

namespace Work.BW

lemma phiIntegralNonpos {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hint : MeasureTheory.Integrable φ)
    (hpeak : ∀ a, 0 ≤ a → ∫ x in Set.Icc (-a) a, φ x ≤ 0) :
    ∫ x, φ x ≤ 0 := by
  have hF : ∀ᶠ a : ℝ in atTop,
      AEStronglyMeasurable (fun x => (Set.Icc (-a) a).indicator φ x) (volume : Measure ℝ) :=
    Filter.Eventually.of_forall (fun a => (hφ.indicator measurableSet_Icc).aestronglyMeasurable)
  have hbound : ∀ᶠ a : ℝ in atTop,
      ∀ᵐ x ∂(volume : Measure ℝ), ‖(Set.Icc (-a) a).indicator φ x‖ ≤ ‖φ x‖ :=
    Filter.Eventually.of_forall
      (fun a => Filter.Eventually.of_forall (fun x => norm_indicator_le_norm_self _ _))
  have hlim : ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun a : ℝ => (Set.Icc (-a) a).indicator φ x) atTop (𝓝 (φ x)) :=
    Filter.Eventually.of_forall (fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop |x|] with a ha
      rw [Set.indicator_of_mem (Set.mem_Icc.mpr (abs_le.mp ha))])
  have hmain := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure ℝ))
    (F := fun a x => (Set.Icc (-a) a).indicator φ x) (f := φ) (bound := fun x => ‖φ x‖)
    hF hbound hint.norm hlim
  simp only [integral_indicator measurableSet_Icc] at hmain
  exact le_of_tendsto hmain (Filter.eventually_atTop.mpr ⟨0, fun a ha => hpeak a ha⟩)

end Work.BW
