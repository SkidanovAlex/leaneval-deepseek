import Mathlib

namespace Work.Mostow

open MeasureTheory
open scoped ENNReal Pointwise

set_option linter.unusedVariables false

/-- A fundamental domain is a set of least measure among the measurable sets meeting almost every
orbit. Proof idea: `μ E = ∑' g, μ (E ∩ g • D)` (`IsFundamentalDomain.measure_eq_tsum'`), while the
covering hypothesis gives `D ⊆ᵃᵉ ⋃ g, (g⁻¹ • E ∩ D)`, so
`μ D ≤ ∑' g, μ (g⁻¹ • E ∩ D) = ∑' g, μ (E ∩ g • D) = μ E`. -/
theorem measureFundLeOrbit {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) [Countable G] [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]
    {D E : Set α} (hD : IsFundamentalDomain G D μ) (hE : MeasurableSet E)
    (hcov : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ E) : μ D ≤ μ E := by
  -- The translates `g⁻¹ • E` cover almost all points, hence `D` is covered a.e. by
  -- `g⁻¹ • E ∩ D`; intersecting with `D` is what makes the resulting series summable
  -- in the right way.
  have hcover : D ≤ᵐ[μ] ⋃ g : G, (g⁻¹ • E ∩ D) := by
    filter_upwards [hcov] with x hx hxD
    obtain ⟨g, hg⟩ := hx
    exact Set.mem_iUnion.mpr ⟨g, ⟨Set.mem_inv_smul_set_iff.mpr hg, hxD⟩⟩
  calc
    μ D ≤ μ (⋃ g : G, (g⁻¹ • E ∩ D)) := measure_mono_ae hcover
    _ ≤ ∑' g : G, μ (g⁻¹ • E ∩ D) := measure_iUnion_le _
    _ = ∑' g : G, μ (E ∩ g • D) := by
        refine tsum_congr fun g => ?_
        rw [← measure_smul μ g (g⁻¹ • E ∩ D), Set.smul_set_inter, smul_inv_smul]
    _ = μ E := (hD.measure_eq_tsum' E).symm

end Work.Mostow
