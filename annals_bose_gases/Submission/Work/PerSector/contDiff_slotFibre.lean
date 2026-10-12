import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
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

/-- **The fibre of a smooth state is smooth.**  Freezing the outside coordinates `y` exhibits the
particle-number sector piece as a `k`-particle function on the box, and if `Φ` is smooth on the
`N`-particle configuration space then its fibre `z ↦ Φ (slotComb S z y)` is smooth on the
`k`-particle configuration space `SlotIn N S → ℝ³`.  This is what makes the fibre a legitimate
trial state for the per-box bounds (`Work.BlockBound4.diagWeBAt`), whose trial space is the smooth
box states. -/
theorem contDiff_slotFibre (S : Finset (Fin N)) {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (y : SlotOut N S → ℝ³) :
    ContDiff ℝ ∞ (slotFibre S Φ y) := by
  -- `z ↦ slotComb S z y` is affine (indeed linear) in `z`: coordinatewise it is either the
  -- projection `z ↦ z ⟨i, _⟩` (when `i ∈ S`) or the constant `y ⟨i, _⟩`.
  have hsmooth : ContDiff ℝ ∞ (fun z : SlotIn N S → ℝ³ => slotComb S z y) := by
    rw [contDiff_pi]
    intro i
    by_cases h : i ∈ S
    · have hfun : (fun z : SlotIn N S → ℝ³ => slotComb S z y i) = fun z => z ⟨i, h⟩ := by
        funext z
        rw [slotComb_apply, dif_pos h]
      rw [hfun]
      exact ContinuousLinearMap.contDiff
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : SlotIn N S => ℝ³) ⟨i, h⟩)
    · have hfun : (fun z : SlotIn N S → ℝ³ => slotComb S z y i) = fun _ => y ⟨i, h⟩ := by
        funext z
        rw [slotComb_apply, dif_neg h]
      rw [hfun]
      exact contDiff_const
  change ContDiff ℝ ∞ (fun z => Φ (slotComb S z y))
  simpa only [Function.comp_def] using hΦ.comp hsmooth

end Work.PerSector

open Submission BoseGases

variable {N : ℕ}

/-- **The fibre of a smooth state is smooth**, re-exported at the chapter's outer namespace
`Work.PerSector` (the declaration proved above sits in the doubly nested namespace produced by this
file's header). -/
theorem contDiff_slotFibre (S : Finset (Fin N)) {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (y : SlotOut N S → EuclideanSpace ℝ (Fin 3)) :
    ContDiff ℝ ∞ (slotFibre S Φ y) :=
  Work.PerSector.Work.PerSector.contDiff_slotFibre S hΦ y

end Work.PerSector
