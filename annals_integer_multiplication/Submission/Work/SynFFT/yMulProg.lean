import Mathlib
import Submission.Work.SynFFT.defs
import Submission.Work.SynFFT.kit

/-!
# SynFFT: the "multiply an `R`-element by a scalar" word

`qMulP uncP pickP mulP rollP swapP consP` is the subroutine used by `hasYMul`: applied to a stack
`cfxVal (a,b) :: int m :: rest`, it unpacks the coefficient vector `(a,b)`, multiplies both
coefficients by the scalar `m` sitting at index `0` of the tail, and re-packs the result:

`cfxVal (a,b) :: int m :: rest  ↦  cfxVal (m*a, m*b) :: int m :: rest`.

The parameters `uncP`, `pickP`, `mulP`, `rollP`, `swapP`, `consP` are the `KernelLib` / `IntLib`
words (`unconsV`, `pick`, `mulS`, `roll`, `swap`, `consV`); the word is thus a function of the
library hypotheses.  Picks are at index `2` (both times) because after `unconsV` the scalar `m`
sits at index `2`, and after the first `mulS` it sits at index `2` again.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-- The multiplier word (see the module docstring). -/
def qMulP (uncP : Cmd) (pickP : ℕ → Cmd) (mulP : Cmd) (rollP : ℕ → Cmd)
    (swapP : Cmd) (consP : Cmd) : Cmd :=
  (((((((uncP ;;; pickP 2) ;;; mulP) ;;; pickP 2) ;;; rollP 2) ;;; swapP) ;;; mulP) ;;; swapP) ;;; consP

end Work.SynFFT
