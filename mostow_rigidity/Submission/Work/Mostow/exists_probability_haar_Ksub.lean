import Mathlib
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.Ksub_compact

namespace Work.Mostow

open MeasureTheory LeanEval.Geometry.MostowRigidity
open scoped ENNReal

set_option linter.style.haveILetI false

/-- The stabiliser `Ksub n hA` of the origin is compact (`Ksub_compact`), hence the compact
group `↥(Ksub n hA)` carries a Haar measure; normalising that Haar measure by the (finite,
nonzero) mass of the whole group turns it into a probability Haar measure.

Concretely, `Measure.haar` is a Haar measure on any locally compact group
(`Measure.isHaarMeasure_haarMeasure`), and `IsHaarMeasure.smul` says that a nonzero finite
scalar multiple of a Haar measure is again a Haar measure.  Taking `c = 1 / μ(univ)` therefore
produces a Haar measure of total mass `1`.

This is needed for the Haar bridge: a probability Haar measure `τ` on `Ksub` lets one turn the
Haar measure of `PO n 1` into the product of `volH` with `τ` via the parametrisation `Theta`. -/
theorem exists_probability_haar_Ksub (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hK : IsCompact (Work.Mostow.Ksub n hA : Set (LeanEval.Geometry.MostowRigidity.PO n 1))) :
    ∃ τ : MeasureTheory.Measure ↥(Work.Mostow.Ksub n hA),
      MeasureTheory.IsProbabilityMeasure τ ∧ MeasureTheory.Measure.IsHaarMeasure τ := by
  classical
  -- `Ksub` is compact, so its subtype is a compact (hence locally compact) group.
  haveI : CompactSpace ↥(Ksub n hA) :=
    (isCompact_iff_compactSpace (s := (Ksub n hA : Set (PO n 1)))).mp hK
  haveI : Measure.IsHaarMeasure (Measure.haar : Measure ↥(Ksub n hA)) := inferInstance
  -- The Haar measure of a compact nonempty group gives finite positive mass to the whole group.
  have h0 : (Measure.haar : Measure ↥(Ksub n hA)) Set.univ ≠ 0 :=
    Measure.IsOpenPosMeasure.open_pos Set.univ isOpen_univ ⟨1, trivial⟩
  have htop : (Measure.haar : Measure ↥(Ksub n hA)) Set.univ ≠ ⊤ :=
    (isCompact_univ.measure_lt_top).ne
  -- Normalise: `τ = μ(univ)⁻¹ • μ`.
  refine ⟨((Measure.haar : Measure ↥(Ksub n hA)) Set.univ)⁻¹ •
      (Measure.haar : Measure ↥(Ksub n hA)), ?_, ?_⟩
  · -- Total mass: `c * μ(univ) = μ(univ)⁻¹ * μ(univ) = 1`.
    rw [isProbabilityMeasure_iff, Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel h0 htop]
  · -- It is still a Haar measure, because it is a finite nonzero scalar multiple of one.
    exact Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr h0)

end Work.Mostow
