import Mathlib
import Submission.Work.Compiler.Defs

namespace Work.Compiler

open HvdH Turing

/-- The halting configuration of the compiled machine, as used by the simulation. -/
theorem haltList_toTM2 (code : List Work.Compiler.Instr) (out : List Bool) :
    Turing.haltList (Work.Compiler.toTM2 code) out =
      ⟨none, Work.Compiler.initMS code, Work.Compiler.toStk code (HvdH.initState []) [] out []⟩ := by
  unfold Turing.haltList Work.Compiler.toTM2 Work.Compiler.toStk HvdH.initState
  congr 1
  funext k
  rcases k with (k | k)
  · simp
  · fin_cases k <;> simp

end Work.Compiler
