import Mathlib
import Submission.Work.Misiurewicz.exists_null_frontier_Vball_radius
import Submission.Work.Misiurewicz.exists_V_mul_inv_subset
import Submission.Work.Misiurewicz.Vball_mem_nhds
import Submission.Work.EKLNonExc.VFacts
import Submission.Work.EKLComp.Misiurewicz.Defs

namespace Work.Misiurewicz

open Work.EKLContract Work.EKLComp

/-- For every `ε > 0`, every finite Borel measure `ν` on `X₃` and every `x ∈ X₃` there is an
open neighbourhood `U` of `x` which is `ε`-fine (`Fine ε U`, i.e. any two of its points are
related by `V ε`) and whose frontier is `ν`-null.

Indeed, pick `η > 0` with `V η · (V η)⁻¹ ⊆ V ε`, so that every translate `Vball η z` is `ε`-fine
(`fine_Vball`).  By the classical no-jump argument, some radius `r ∈ (0, η]` has `ν`-null frontier
on `Vball r x` (`exists_null_frontier_Vball_radius`).  Then `U := Vball r x` is an open
neighbourhood of `x`, and it is `ε`-fine because `Vball r x ⊆ Vball η x` and `Fine ε` is inherited
by subsets. -/
theorem exists_fine_null_frontier_nhd (ε : ℝ) (hε : 0 < ε)
    (ν : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsFiniteMeasure ν]
    (x : Work.EKLContract.X3) :
    ∃ U : Set Work.EKLContract.X3,
      IsOpen U ∧ x ∈ U ∧ Work.EKLComp.Fine ε U ∧ ν (frontier U) = 0 := by
  -- a modulus `η > 0` making every `η`-ball `ε`-fine
  obtain ⟨η, hηpos, hη⟩ := exists_V_mul_inv_subset ε hε
  have hFineη : Fine ε (Vball η x) := fine_Vball ε η hη x
  -- a radius `r ∈ (0, η]` with `ν`-null frontier
  obtain ⟨r, hrpos, hrle, hfr⟩ := exists_null_frontier_Vball_radius ν x hηpos
  refine ⟨Vball r x, isOpen_Vball x hrpos, ?_, ?_, hfr⟩
  · exact mem_of_mem_nhds (Vball_mem_nhds r hrpos x)
  · exact fun a ha b hb => hFineη a (Vball_mono x hrle ha) b (Vball_mono x hrle hb)

end Work.Misiurewicz
