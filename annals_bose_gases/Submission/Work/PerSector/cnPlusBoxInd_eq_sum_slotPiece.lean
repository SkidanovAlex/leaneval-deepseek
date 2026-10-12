import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.sq_boxQInd_eq_sum_sq_boxQInd_slotPiece
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PerSector

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.PerSector

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

variable {N : ℕ}

/-- **The box excited count is slot-additive.**  The `abox`-`L²`-mass of FS's projection
`Q_{A,i}Φ` is the sum of the masses of its projections of the slot pieces: the pointwise identity
`(Q_{A,i}Φ x)² = Σ_S (Q_{A,i}(slotPiece A S Φ) x)²`
(`sq_boxQInd_eq_sum_sq_boxQInd_slotPiece`) is integrated over `abox N a`, using the finiteness of the
finite sum (`IntegrableOn` of each summand and of the whole).  This is the `n₊(B)` half of the slot
additivity of the localised kinetic word. -/
theorem cnPlusBoxInd_eq_sum_slotPiece {N : ℕ} {A : Set ℝ³} (hA : MeasurableSet A)
    {volA a : ℝ} (i : Fin N) {Φ : X N → ℝ}
    (hint : ∀ S : Finset (Fin N), MeasureTheory.IntegrableOn
      (fun x => (Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ) x) ^ 2)
      (Submission.BoseGases.abox N a))
    (hint0 : MeasureTheory.IntegrableOn (fun x => (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      (Submission.BoseGases.abox N a)) :
    ∫ x in Submission.BoseGases.abox N a, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
      = ∑ S : Finset (Fin N),
          ∫ x in Submission.BoseGases.abox N a,
            (Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ) x) ^ 2 := by
  -- The right-hand side is the integral of the finite sum of the summands, since each summand is
  -- integrable on the box.
  rw [← integral_finsetSum]
  · -- The integrand of the left-hand side is that finite sum, pointwise on the whole space.
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun x => sq_boxQInd_eq_sum_sq_boxQInd_slotPiece hA i x)
  · intro S _
    exact hint S

end Work.PerSector

open Submission BoseGases

variable {N : ℕ}

/-- **The box excited count is slot-additive**, re-exported at the chapter's outer namespace
`Work.PerSector` (the declaration proved above sits in the doubly nested namespace produced by this
file's header). -/
theorem cnPlusBoxInd_eq_sum_slotPiece
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    {volA a : ℝ} (i : Fin N) {Φ : X N → ℝ}
    (hint : ∀ S : Finset (Fin N), MeasureTheory.IntegrableOn
      (fun x => (Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ) x) ^ 2)
      (Submission.BoseGases.abox N a))
    (hint0 : MeasureTheory.IntegrableOn (fun x => (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      (Submission.BoseGases.abox N a)) :
    ∫ x in Submission.BoseGases.abox N a, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
      = ∑ S : Finset (Fin N),
          ∫ x in Submission.BoseGases.abox N a,
            (Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ) x) ^ 2 :=
  Work.PerSector.Work.PerSector.cnPlusBoxInd_eq_sum_slotPiece hA i hint hint0

end Work.PerSector
