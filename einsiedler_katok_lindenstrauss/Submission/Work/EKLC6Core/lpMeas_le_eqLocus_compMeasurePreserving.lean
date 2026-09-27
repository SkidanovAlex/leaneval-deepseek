import Mathlib

open scoped MeasureTheory

namespace Work.EKLC6Core

/-- If an `L²` function is a.e. measurable for the σ-algebra of `T`-invariant sets, then composing
it with the measure preserving map `T` does not change it. -/
theorem lpMeas_le_eqLocus_compMeasurePreserving {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (T : X → X) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (g : MeasureTheory.Lp ℝ 2 μ)
    (hg : g ∈ MeasureTheory.lpMeas ℝ ℝ (MeasurableSpace.invariants T) 2 μ) :
    MeasureTheory.Lp.compMeasurePreserving T hmp g = g := by
  apply MeasureTheory.Lp.ext
  -- `g` is a.e. equal to a function `g'` that is strongly measurable for `invariants T`.
  have hae : AEStronglyMeasurable[MeasurableSpace.invariants T] (g : X → ℝ) μ :=
    MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable.mp hg
  obtain ⟨g', hg'strong, hg'eq⟩ := hae
  -- `g'` is invariant under `T`, because it is measurable for `invariants T`.
  have hg'meas : Measurable[MeasurableSpace.invariants T] g' := hg'strong.measurable
  have hg'T : g' ∘ T = g' := MeasurableSpace.comp_eq_of_measurable_invariants hg'meas
  have h1 : ((g : X → ℝ) ∘ T) =ᵐ[μ] g' := by
    rw [← hg'T]
    exact (MeasureTheory.MeasurePreserving.quasiMeasurePreserving hmp).ae_eq hg'eq
  calc
    (↑↑(MeasureTheory.Lp.compMeasurePreserving T hmp g) : X → ℝ)
        =ᵐ[μ] (g : X → ℝ) ∘ T :=
      MeasureTheory.Lp.coeFn_compMeasurePreserving g hmp
    _ =ᵐ[μ] g' := h1
    _ =ᵐ[μ] (g : X → ℝ) := hg'eq.symm

end Work.EKLC6Core
