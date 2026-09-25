import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

namespace Commons.Analysis.Measure

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

/-- An `L^p` function has a *measurable* representative which agrees with it almost
everywhere.  This is used to replace the a.e.-measurable function of the challenge by a
genuinely measurable one when invoking the transference lemmas. -/
theorem memLp_exists_measurable_ae_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {p : ℝ≥0∞} (hf : MemLp f p μ) :
    ∃ f' : X → ℝ, Measurable f' ∧ f' =ᵐ[μ] f := by
  obtain ⟨g, hg, hfg⟩ := hf.aemeasurable
  exact ⟨g, hg, hfg.symm⟩

end Commons.Analysis.Measure