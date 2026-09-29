import Submission.Work.Compiler.Sim2
import Submission.Work.Compiler.initList_toTM2
import Submission.Work.Compiler.haltList_toTM2

/-!
# A reducible `FinTM2` bundle

`toTM2 code` is a semireducible definition, so the types `(toTM2 code).Γ ((toTM2 code).k₀)` do not
reduce by projection during rewriting.  `tmP code` is the same structure, made an `abbrev`, so its
projections reduce definitionally; this is essential for rewriting the input/output lists.
-/

set_option autoImplicit false

namespace Work.Compiler

open HvdH Turing StateTransition

/-- The compiled machine, as a reducible bundle. -/
abbrev tmP (code : List Instr) : FinTM2 :=
  { K := KK, kDecidableEq := inferInstance, kFin := inferInstance, k₀ := Sum.inr 0, k₁ := Sum.inr 1,
    Γ := Γ code, Λ := Λ code, main := labA code, ΛFin := inferInstance, σ := MS code,
    initialState := initMS code, σFin := inferInstance, Γk₀Fin := inferInstance, m := mach code }

theorem initList_tmP (code : List Instr) (w : List InSym) :
    initList (tmP code) w =
      ⟨some (labA code), initMS code, toStk code (initState []) w [] []⟩ :=
  initList_toTM2 code w

theorem haltList_tmP (code : List Instr) (out : List Bool) :
    haltList (tmP code) out =
      ⟨none, initMS code, toStk code (initState []) [] out []⟩ :=
  haltList_toTM2 code out

end Work.Compiler
