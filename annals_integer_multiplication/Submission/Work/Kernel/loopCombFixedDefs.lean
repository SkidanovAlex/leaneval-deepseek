import Mathlib
import Submission.Work.Kernel.Raw

/-!
# Kernel: the `loop` combinator of `KernelLib` (with the missing hypothesis `1 ≤ m`)

`KernelLib.loop` (`Submission/HvdH/Interfaces.lean`) bounds the run of the generated do-while by
`m * (c + K) + K` for arbitrary `m`, but the generated program is a do-while: it runs `q` at least
once.  At `m = 0` the bound degenerates to the constant `K`, which is impossible (see
`Submission/Work/Kernel/loopRefute.lean`).  The repair, proved in
`Submission/Work/Kernel/loopCombFixed.lean`, adds the hypothesis `1 ≤ m`.

Here we only record the *program*: the combinator runs `q`, reads the flag glyphs of the `int` on
top of stack 0 (`Val.enc (.int 0) = [pos, iend]`, `Val.enc (.int 1) = [pos, bit true, iend]`), and
continues exactly when the flag was `int 1`.

Register 0 is the loop-test register (test constant `Glyph.eos`), register 1 is a scratch.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-- One round of the do-while: run `q`, then consume the flag value `int 0` / `int 1` it pushed on
top of stack 0, setting register 0 to `Glyph.eos` (continue) or to `Glyph.iend` (stop). -/
def loopCombFixed_body (q : Cmd) : Cmd :=
  Cmd.seq q (Cmd.seq (Cmd.pop 0 1) (Cmd.seq (Cmd.pop 0 1)
    (Cmd.ite 1 Glyph.iend (Cmd.set 0 Glyph.iend)
      (Cmd.seq (Cmd.pop 0 1) (Cmd.set 0 Glyph.eos)))))

/-- The `loop` combinator: arm the test register (cost 1) and run the do-while. -/
def loopCombFixed_comb (q : Cmd) : Cmd :=
  Cmd.seq (Cmd.set 0 Glyph.eos) (Cmd.loop 0 Glyph.eos (loopCombFixed_body q))

end Work.Kernel
