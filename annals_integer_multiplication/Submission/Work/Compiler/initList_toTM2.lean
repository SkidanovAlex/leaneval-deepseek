import Mathlib
import Submission.Work.Compiler.Defs

/-!
# The initial configuration of the compiled machine

`Submission/Work/Compiler/Defs.lean` defines the machine `toTM2 code` running a flat instruction
list, and this file checks that Mathlib's `Turing.initList` for it is exactly the configuration
that the simulation proof (`compilerThm`) starts from: the algorithm's own initial `HvdH.State`
placed on the language stacks, the input word on the input stack, and nothing else.

The only point needing care is the `dite` in the definition of `Turing.initList`, which moves the
input list from the input stack `tm.k₀ = Sum.inr 0` to an arbitrary stack `k` by a transport along
`k = tm.k₀`.  For `k = Sum.inr 0` this transport is along an equation between *definitionally
equal* types (both are `List HvdH.InSym`), so it is the identity: that is the content of the helper
`eq_mpr_self`. -/

set_option autoImplicit false

namespace Work.Compiler

open HvdH

/-- Transporting an element along an equation between a type and itself is the identity.

Note that `h` need not be `rfl` for this to apply: the point is that the two types occurring in
`h` only have to be *definitionally* equal for the statement to elaborate. -/
private theorem eq_mpr_self.{u} {α : Sort u} (h : α = α) (a : α) : @Eq.mpr α α h a = a := by
  cases h; rfl

/-- The initial configuration of the compiled machine, as used by the simulation. -/
theorem initList_toTM2 (code : List Work.Compiler.Instr) (w : List HvdH.InSym) :
    Turing.initList (Work.Compiler.toTM2 code) w =
      ⟨some (Work.Compiler.labA code), Work.Compiler.initMS code,
        Work.Compiler.toStk code (HvdH.initState []) w [] []⟩ := by
  simp only [Turing.initList, toTM2]
  dsimp only [Turing.FinTM2.Cfg]
  rw [Turing.TM2.Cfg.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext k
  -- `k = Sum.inl j`: `initList` stores `[]` there, and so does `HvdH.initState []`.
  cases k with
  | inl k => simp [toStk, HvdH.initState]
  -- `k = Sum.inr j`: only `Sum.inr 0` (the input stack) carries data.
  | inr k =>
      fin_cases k <;> simp [toStk]
      exact eq_mpr_self _ w

end Work.Compiler
