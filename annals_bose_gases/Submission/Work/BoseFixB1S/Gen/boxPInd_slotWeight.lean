import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.Gen

open MeasureTheory

/-- **The box projection in slot `j` commutes with a weight in slot `i ≠ j`.**  Because the
fibre `z ↦ Function.update x j z` never moves slot `i`, the function `y ↦ w (y i) * Ψ y`
restricts to `w (x i) * Ψ` along that fibre, and the constant `w (x i)` comes out of the
`A`-integral. -/
theorem boxPInd_slotWeight {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {w : EuclideanSpace ℝ (Fin 3) → ℝ} {i j : Fin N} (hij : i ≠ j)
    (Ψ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A j (fun y => w (y i) * Ψ y) x
      = w (x i) * Work.UBBInputs8.boxPInd volA A j Ψ x := by
  have hInt : (∫ z in A, (fun y : Submission.BoseGases.X N => w (y i) * Ψ y)
        (Function.update x j z))
      = w (x i) * (∫ z in A, Ψ (Function.update x j z)) := by
    have hfun : (fun z : EuclideanSpace ℝ (Fin 3) =>
          (fun y : Submission.BoseGases.X N => w (y i) * Ψ y) (Function.update x j z))
        = fun z => w (x i) * Ψ (Function.update x j z) := by
      funext z
      change w ((Function.update x j z) i) * Ψ (Function.update x j z)
        = w (x i) * Ψ (Function.update x j z)
      rw [Function.update_of_ne hij]
    rw [hfun, MeasureTheory.integral_const_mul]
  simp only [Work.UBBInputs8.boxPInd]
  rw [hInt]
  ring

end Work.BoseFixB1S.Gen
