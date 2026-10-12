import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.PerSector.Strat
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

/-- **The slot reassembly is jointly measurable.**  Reassembling a configuration from its in-box and
outside slot coordinates is nothing but the inverse of the measurable splitting equivalence
`slotEquiv S = Equiv.piEquivPiSubtypeProd (· ∈ S) (fun _ => ℝ³)`, so it is measurable for the Borel
structures on the (finite) configuration spaces. -/
theorem measurable_slotComb (S : Finset (Fin N)) :
    Measurable (fun p : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) => slotComb S p.1 p.2) := by
  simpa only [slotComb, slotEquiv] using
    (measurable_piEquivPiSubtypeProd_symm (fun _ : Fin N => ℝ³) (fun i : Fin N => i ∈ S))

/-- **The fibre field is jointly measurable.**  The map `(z, y) ↦ Φ (slotComb S z y)` is measurable
on the product of the in-box and outside slot configurations; this is the measurability input of the
Fubini decomposition `slotMassENN_eq_fibre`. -/
theorem measurable_slotFibre_pair (S : Finset (Fin N)) {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun p : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) => Φ (slotComb S p.1 p.2)) :=
  hΦ.comp (measurable_slotComb S)

end Work.PerSector

open Submission BoseGases

variable {N : ℕ}

/-- **The fibre field is jointly measurable**, re-exported at the chapter's outer namespace
`Work.PerSector` (the declaration proved above sits in the doubly nested namespace produced by this
file's header). -/
theorem measurable_slotFibre_pair (S : Finset (Fin N)) {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun p : (SlotIn N S → EuclideanSpace ℝ (Fin 3)) ×
      (SlotOut N S → EuclideanSpace ℝ (Fin 3)) => Φ (slotComb S p.1 p.2)) :=
  Work.PerSector.Work.PerSector.measurable_slotFibre_pair S hΦ

end Work.PerSector
