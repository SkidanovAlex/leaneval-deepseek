import Mathlib
import Submission.Work.Kernel.Raw

/-!
# Kernel: programs and states for the `ifZero` word

Definitions only (no proofs) for `Work.Kernel.ifZero`, so that the assembly and the lemma about the
drain loop can be developed in parallel.

`Val.enc (.int z)` is the sign glyph, then the bits of `|z|` least significant first
(`encodeNat`, which is `[]` for `0`), then `iend`.  Hence the integer on top of stack 0 is `0` iff
the glyph after the sign is `iend`; otherwise the remaining bits must be drained before the
continuation runs.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-- Body of the drain loop: pop the top glyph of stack `0` into `r`; if it was `Glyph.iend`,
leave it in `r` (so that the loop test `reg r = Glyph.eos` fails and the loop stops), otherwise
reset `r` to `Glyph.eos` (the loop test constant) so that the loop continues. -/
def ifZero_drainBody (r : Reg) : Cmd :=
  Cmd.seq (Cmd.pop 0 r) (Cmd.ite r Glyph.iend Cmd.skip (Cmd.set r Glyph.eos))

/-- The drain loop: starting from `reg r = Glyph.eos`, pop glyphs of stack `0` up to and including
the first `Glyph.iend`. -/
def ifZero_drainLoop (r : Reg) : Cmd := Cmd.loop r Glyph.eos (ifZero_drainBody r)

/-- `set r Glyph.eos` followed by the drain loop. -/
def ifZero_drain (r : Reg) : Cmd := Cmd.seq (Cmd.set r Glyph.eos) (ifZero_drainLoop r)

/-- The state reached by `ifZero_drain r` when stack `0` held `ms.map bit` then `iend` then `R`:
stack `0` is `R` and `r` holds `Glyph.iend`. -/
def ifZero_drainState (r : Reg) (R : List Glyph) (s : State) : State :=
  (s.updStk 0 R).updReg r Glyph.iend

/-- The zero test with scratch register `r`: consume the sign glyph and the next glyph; if the
latter is `Glyph.iend` the integer was `0`, so run `q₁`, otherwise drain the remaining bits and run
`q₂`.  Both continuations see the integer consumed. -/
def ifZero_test (r : Reg) (q₁ q₂ : Cmd) : Cmd :=
  Cmd.seq (Cmd.pop 0 r)
    (Cmd.seq (Cmd.pop 0 r) (Cmd.ite r Glyph.iend q₁ (Cmd.seq (ifZero_drain r) q₂)))

/-- The `ifZero` combinator (scratch register `0`). -/
def ifZero_comb (q₁ q₂ : Cmd) : Cmd := ifZero_test 0 q₁ q₂

/-- The state reached by `ifZero_comb q₁ q₂` just after the integer `Val.int z` has been consumed:
stack `0` is `encs rest ++ R` and register `0` holds `Glyph.iend`. -/
def ifZero_afterPrelude (rest : List Val) (R : List Glyph) (s : State) : State :=
  (s.updStk 0 (encs rest ++ R)).updReg 0 Glyph.iend

end Work.Kernel
