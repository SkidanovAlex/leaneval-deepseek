import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- **Linearity of the box projection `Pᵢ` over an arbitrary finite sum.**  For a family of states
whose slot functions are integrable over `A` at `x`, the slot mean of the sum is the sum of the
slot means. -/
theorem boxPInd_finset_sum_gen {ι : Type*} {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N)
    (x : X N) (s : Finset ι) (f : ι → X N → ℝ)
    (h : ∀ j ∈ s, IntegrableOn (fun z => f j (Function.update x i z)) A volume) :
    UBBInputs8.boxPInd volA A i (fun y => ∑ j ∈ s, f j y) x
      = ∑ j ∈ s, UBBInputs8.boxPInd volA A i (f j) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [UBBInputs8.boxPInd]
  | insert a s ha ih =>
    have hfs : (fun y : X N => ∑ j ∈ insert a s, f j y)
        = (fun y => f a y) + (fun y => ∑ j ∈ s, f j y) := by
      funext y
      rw [Finset.sum_insert ha]
      rfl
    rw [hfs, boxPInd_add volA A i x (h a (Finset.mem_insert_self a s)) ?_,
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj)), Finset.sum_insert ha]
    exact integrable_finsetSum (μ := (volume : Measure E3).restrict A) s
      (f := fun j => fun z : E3 => f j (Function.update x i z))
      (fun j hj => h j (Finset.mem_insert_of_mem hj))

end Work.BoseFixB1S
