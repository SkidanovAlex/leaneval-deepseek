import Mathlib

open scoped Pointwise

namespace Work.Mostow

/-- If `S` is a measurable `G`-invariant set and `D` is a fundamental domain for the action of `G`
on `α` with respect to `μ`, then `S ∩ D` is a fundamental domain for the action restricted to `S`,
i.e. for the measure `μ.restrict S`. -/
theorem fundamentalDomain_inter_invariant {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasurableConstSMul G α]
    [MeasureTheory.SMulInvariantMeasure G α μ] {S D : Set α} (hS : MeasurableSet S)
    (hSinv : ∀ g : G, (fun x => g • x) '' S = S) (hD : MeasureTheory.IsFundamentalDomain G D μ) :
    MeasureTheory.IsFundamentalDomain G (S ∩ D) (μ.restrict S) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (hS.nullMeasurableSet.inter hD.nullMeasurableSet).mono_ac
      MeasureTheory.Measure.absolutelyContinuous_restrict
  · have h1 : ∀ᵐ x ∂(μ.restrict S), ∃ g : G, g • x ∈ D :=
      MeasureTheory.ae_restrict_of_ae hD.ae_covers
    have h2 : ∀ᵐ x ∂(μ.restrict S), x ∈ S := MeasureTheory.ae_restrict_mem hS
    exact (h1.and h2).mono fun x hx => by
      obtain ⟨⟨g, hg⟩, hxS⟩ := hx
      refine ⟨g, ⟨?_, hg⟩⟩
      have himg : g • x ∈ (fun x => g • x) '' S := ⟨x, hxS, rfl⟩
      rwa [hSinv g] at himg
  · intro g₁ g₂ hne
    refine ((hD.aedisjoint hne).mono ?_ ?_).of_le MeasureTheory.Measure.restrict_le_self
    · exact Set.smul_set_mono Set.inter_subset_right
    · exact Set.smul_set_mono Set.inter_subset_right

end Work.Mostow
