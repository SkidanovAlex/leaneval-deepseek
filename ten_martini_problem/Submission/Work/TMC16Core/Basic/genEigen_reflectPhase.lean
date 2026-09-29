import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Basic

/-- The quasi-periodic potential is invariant under reversing the sign of the phase while
reversing the site index: `v_{-θ}(n) = v_θ(-n)`.  (Both sides equal
`2λ cos(2π(θ - nα))`, using that `cos` is even.) -/
theorem amoPot_neg_phase (α lam θ : ℝ) (n : ℤ) :
    Work.TMC16Core.amoPot α lam (-θ) n = Work.TMC16Core.amoPot α lam θ (-n) := by
  simp only [Work.TMC16Core.amoPot]
  rw [show 2 * Real.pi * (-θ + (n : ℝ) * α)
        = -(2 * Real.pi * (θ + ((-n : ℤ) : ℝ) * α)) from by push_cast; ring, Real.cos_neg]

/-- The action of the operator with phase `-θ` on the reflected sequence `n ↦ u (-n)`
agrees with the action with phase `θ` on `u`, reflected. -/
theorem amoAct_neg_phase (α lam θ : ℝ) (u : ℤ → ℂ) (n : ℤ) :
    Work.TMC16Core.amoAct α lam (-θ) (fun m => u (-m)) n
      = Work.TMC16Core.amoAct α lam θ u (-n) := by
  simp only [Work.TMC16Core.amoAct]
  rw [amoPot_neg_phase]
  ring_nf

/-- **Reflection of the phase.**  If `u` is a generalized eigenfunction of the almost Mathieu
operator with phase `θ`, then its reflection `n ↦ u (-n)` is a generalized eigenfunction for
the phase `-θ` with the same energy. -/
theorem genEigen_reflectPhase {α lam θ E : ℝ} {u : ℤ → ℂ} (hu : Work.TMC16Core.IsGenEigen α lam θ E u) : Work.TMC16Core.IsGenEigen α lam (-θ) E (fun n => u (-n)) := by
  obtain ⟨hu0, hrec, hbound⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hu0
    funext m
    simpa using congrFun h (-m)
  · intro n
    rw [amoAct_neg_phase]
    exact hrec (-n)
  · obtain ⟨C, hC⟩ := hbound
    refine ⟨C, ?_⟩
    intro n
    simpa using hC (-n)

end Work.TMC16Core.Basic
