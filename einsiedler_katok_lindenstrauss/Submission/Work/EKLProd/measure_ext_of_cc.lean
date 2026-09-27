import Mathlib

/-!
# Two locally finite measures agreeing on `C_c` integrals are equal

This is the "Riesz uniqueness" input used throughout C5b: the leafwise measures are known to us
only through integrals against compactly supported continuous test functions (the `condexp`
field of `IsLeafwise`), so to convert an equality of integrals into an equality of measures one
needs that `C_c(X,ℝ)` separates locally finite Borel measures on a σ-compact locally compact
(pseudo)metrizable space; there regularity is automatic
(`MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`), so Mathlib's
`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported` applies.

Used at the end of Pisa 8.5 (step 3, `EKLProd/nuT_class_of_mem_shape`) and in the
product-structure step of `EKLComp/prove_Product`.
-/

open MeasureTheory

namespace Work.EKLProd

theorem measure_ext_of_cc {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]
    [LocallyCompactSpace X] (μ ν : Measure X) [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts ν]
    (h : ∀ f : CompactlySupportedContinuousMap X ℝ, ∫ x, (f : X → ℝ) x ∂μ
      = ∫ x, (f : X → ℝ) x ∂ν) : μ = ν := by
  haveI : MeasureTheory.Measure.Regular μ :=
    MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  haveI : MeasureTheory.Measure.Regular ν :=
    MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  exact MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported h

end Work.EKLProd
