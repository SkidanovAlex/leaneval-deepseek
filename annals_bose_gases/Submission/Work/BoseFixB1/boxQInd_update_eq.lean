import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

theorem boxQInd_update_eq {n : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (i : Fin n)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Work.UBBInputs8.boxQInd volA A i Ψ (Function.update x i z)
      = A.indicator (fun _ => 1) z * (Ψ (Function.update x i z)
          - (1 / volA) * ∫ w in A, Ψ (Function.update x i w)) := by
  -- Unfold `boxQInd = 1_A(x_i)·Φ − (1/volA)∫_A Φ(x_i↦w)·1_A(x_i)` at `x := update x i z`.
  -- The slot indicator evaluates to `1_A z`, and the inner integral
  -- `∫_A Ψ (update (update x i z) i w)` collapses to `∫_A Ψ (update x i w)`.
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Function.update_self,
    Function.update_idem]
  ring

end Work.BoseFixB1
