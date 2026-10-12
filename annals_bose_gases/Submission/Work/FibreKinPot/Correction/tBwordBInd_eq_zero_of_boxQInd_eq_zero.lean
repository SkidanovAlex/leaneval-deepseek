import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FibreWord.SliceAE
import Submission.Work.FibreWord.fibPiece_ae_eq_zero_of_fibMass_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FibreKinPot.Correction

/-!
# The sliding kinetic word vanishes when the box projectors do

The FS-faithful sliding word `Work.UBBInputs8.tBwordBInd` is a linear combination of two
functionals of the box-mean-free projections `Q_{B(u),i}Ψ = boxQInd (boxMass L d u) (dlBox L d u) i Ψ`:

* the excited count `Work.UBBInputs8.cnPlusBoxInd`, which integrates the *square* of `Q_{B(u),i}Ψ`
  over the ambient box;
* the `p`-diagonal spectral form `Work.UBBInputs8.tBdiagFormInd`, built from the windowed amplitude
  `Work.SmallBoxTBWord.tBamp (chiB L d u) p (Q_{B(u),i}Ψ)`, which is linear in its state.

So if every `Q_{B(u),i}Ψ` vanishes identically, both halves of the word vanish and the word is `0`.

This is precisely the vanishing used at the constant state in
`Work.UBBInputs8.A.tBwordBInd_const_zero` (its `hQ`), stated here for an arbitrary state `Ψ` whose
`Q`-projections all vanish — the form the fibre-gluing argument needs.
-/

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- If the `Q_{B,i}` all vanish pointwise, the excited count vanishes: it is a sum of integrals of
squares of the `Q_{B,i}`. -/
private theorem cnPlusBoxInd_eq_zero_of_boxQ_eq_zero {a volA : ℝ} {A : Set ℝ³} {N : ℕ}
    {Ψ : Submission.BoseGases.X N → ℝ}
    (h : ∀ i : Fin N, Work.UBBInputs8.boxQInd volA A i Ψ = 0) :
    Work.UBBInputs8.cnPlusBoxInd a A volA Ψ = 0 := by
  simp only [Work.UBBInputs8.cnPlusBoxInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [h i]
  simp

/-- If the `Q_{B,i}` all vanish pointwise, the `p`-diagonal spectral form vanishes: the windowed
amplitude `tBamp` is linear in its state, so it vanishes on the zero state. -/
private theorem tBdiagFormInd_eq_zero_of_boxQ_eq_zero {a volA : ℝ} {A : Set ℝ³} (χ : ℝ³ → ℝ)
    (F : ℝ → ℝ) {N : ℕ} {Ψ : Submission.BoseGases.X N → ℝ}
    (h : ∀ i : Fin N, Work.UBBInputs8.boxQInd volA A i Ψ = 0) :
    Work.UBBInputs8.tBdiagFormInd a A volA χ F Ψ = 0 := by
  simp only [Work.UBBInputs8.tBdiagFormInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  simp only [h i]
  simp [Work.SmallBoxTBWord.tBamp]

/-- **`tBwordBInd` vanishes if the box-mean-free projections `Q_{B(u),i}Ψ` all vanish.**  Both
halves of `tBwordBInd = tbGapCoeff (L·d) ε · cnPlusBoxInd + tBdiagFormInd` are functionals of the
`Q_{B(u),i}Ψ`, so the word is `0`. -/
theorem tBwordBInd_eq_zero_of_boxQInd_eq_zero {L d ε c : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {k : ℕ} {Ψ : Submission.BoseGases.X k → ℝ}
    (h : ∀ (i : Fin k) (x : Submission.BoseGases.X k),
      Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i Ψ x = 0) :
    Work.UBBInputs8.tBwordBInd k L d ε c u Ψ = 0 := by
  simp only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
    Work.UBBInputs8.tBwordKinInd]
  have hQ : ∀ i : Fin k, Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
      (Submission.BoseGases.dlBox L d u) i Ψ = 0 := fun i => funext (h i)
  rw [cnPlusBoxInd_eq_zero_of_boxQ_eq_zero
      (a := L) (A := Submission.BoseGases.dlBox L d u)
      (volA := Work.SmallBoxSliding.boxMass L d u) hQ,
    tBdiagFormInd_eq_zero_of_boxQ_eq_zero
      (a := L) (A := Submission.BoseGases.dlBox L d u)
      (volA := Work.SmallBoxSliding.boxMass L d u)
      (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) hQ]
  ring

end Work.FibreKinPot.Correction
