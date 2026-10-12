import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
import Submission.Work.FibreKinPot.Correction.tBwordBInd_eq_zero_of_boxQInd_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-!
# The sliding kinetic word vanishes on the far set

On the far set `Work.SmallBoxSliding.farSet ℓ d μ` some coordinate of `w = (ℓd)•u` exceeds the
outer half-side `½ℓ(1+d)`, so FS's small box `B(u) = dlBox ℓ d u = acube ℓ ∩ (w + acube (ℓd))`
is empty (`Work.UBBInputs8.A.dlBox_eq_empty_of_mem_farSet`).  For an empty box the FS-faithful
mean-free projection is the zero function:

    boxQInd volA ∅ i Φ x = 1_∅(x i)·Φ x − (|∅|⁻¹∫_∅ Φ(x_{i←z}) dz)·1_∅(x i) = 0 ,

because *both* terms carry the box indicator `1_∅ = 0` and the inner integral is over `∅`.

Both halves of `tBwordBInd = tbGapCoeff (ℓd) ε · cnPlusBoxInd + tBdiagFormInd` are functionals of
these projections, so the word vanishes —
`Work.FibreKinPot.Correction.tBwordBInd_eq_zero_of_boxQInd_eq_zero`.

This is the `farSet` half of the discarded-set analysis of the sliding localisation (the other
half being the `bandSet`, where the box is nondegenerate and `χ_{B(u)} ≠ 0`): on the far set the
discarded contribution to the localised kinetic word is *exactly* zero, not merely bounded.
-/

set_option linter.unusedVariables false

/-- The FS-faithful box projection `Q_{B(u)}` is the zero function when the box is empty:
both of its terms carry the box indicator. -/
private theorem boxQInd_eq_zero_of_dlBox_eq_empty {ℓ d volA : ℝ} {N : ℕ}
    {u : EuclideanSpace ℝ (Fin 3)} (hbox : Submission.BoseGases.dlBox ℓ d u = ∅) (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxQInd volA (Submission.BoseGases.dlBox ℓ d u) i Φ = 0 := by
  funext x
  simp [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, hbox]

/-- On the far set the sliding box `B(u)` is empty, hence the FS-faithful mean-free projection
`Q_{B(u),i}` vanishes identically and so does the sliding kinetic word `tBwordBInd`. -/
theorem tBwordBInd_eq_zero_of_farSet {n : ℕ} {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : u ∈ Work.SmallBoxSliding.farSet ℓ d 0)
    (Φ : Submission.BoseGases.X n → ℝ) :
    Work.UBBInputs8.tBwordBInd n ℓ d ε c u Φ = 0 := by
  have hbox : Submission.BoseGases.dlBox ℓ d u = ∅ :=
    Work.UBBInputs8.A.dlBox_eq_empty_of_mem_farSet hℓ hd hu
  refine Work.FibreKinPot.Correction.tBwordBInd_eq_zero_of_boxQInd_eq_zero ?_
  intro i x
  have h := congrFun (boxQInd_eq_zero_of_dlBox_eq_empty
    (volA := Work.SmallBoxSliding.boxMass ℓ d u) hbox i Φ) x
  simpa using h

end Work.BoseFixB1
