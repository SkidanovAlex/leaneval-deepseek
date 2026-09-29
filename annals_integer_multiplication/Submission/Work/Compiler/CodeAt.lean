import Mathlib
import Submission.Work.Compiler.Defs

/-!
# The position predicate for compiled blocks

`CodeAt code pc c` says that `code` contains the block `compile c pc` at positions
`pc, pc+1, …, pc + clen c - 1`, with exactly the target labels that `compile c pc` writes into the
branch instructions.  This is the invariant the simulation proof needs: each `Eval` constructor
inspects only the instruction at the current position (and, for `ite`/`loop`, the trailing `jmp`).
-/

set_option autoImplicit false

namespace Work.Compiler

open HvdH

/-- `CodeAt code pc c` records that `compile c pc` sits in `code` at position `pc`. -/
def CodeAt (code : List Instr) : ℕ → Cmd → Prop
  | pc, .skip => code[pc]? = some .skip
  | pc, .pop k r => code[pc]? = some (.pop k r)
  | pc, .peek k r => code[pc]? = some (.peek k r)
  | pc, .push k r => code[pc]? = some (.push k r)
  | pc, .set r c => code[pc]? = some (.set r c)
  | pc, .mov d t => code[pc]? = some (.mov d t)
  | pc, .seq a b => CodeAt code pc a ∧ CodeAt code (pc + clen a) b
  | pc, .ite r c p q =>
      code[pc]? = some (.test r c (pc + clen p + 2)) ∧ CodeAt code (pc + 1) p ∧
      code[pc + clen p + 1]? = some (.jmp (pc + clen p + 2 + clen q)) ∧
      CodeAt code (pc + clen p + 2) q
  | pc, .loop r c b =>
      code[pc]? = some (.test r c (pc + clen b + 2)) ∧ CodeAt code (pc + 1) b ∧
      code[pc + clen b + 1]? = some (.jmp pc)
  | pc, .self => code[pc]? = some .call

end Work.Compiler
