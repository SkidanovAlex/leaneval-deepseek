import Mathlib
import Submission.Work.Resample.auLoopDefs
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auConvDefs
import Submission.Work.Resample.auPrepDefs

/-!
# Definitions for the setup word of the resampling (`Work.Resample.auSetupRun`)

The setup word produces the initial state of the window loop of `Work.Resample.auLoopWord`:

* the window `auWinV p α s t u 0` of the first output on stack 0, below the parameter block
  `auPvals p α s t`;
* the record run `auRecsF p α s t ++ [nil]` on stack 1;
* the element run `auElems p α s u ++ [nil]` on stack 2;
* the empty chunk run `[nil]` on stack 3.

This module fixes the data it manipulates.  Nothing here is a program.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The glyph-level flag of a slide: `nil` for `0`, a `cons`-value otherwise. -/
def auSetupFlag (g : ℤ) : Val := if g = 0 then .nil else .cons .nil .nil

/-- The value-level operation of the record word on one record:
`cons (int g) w ↦ cons (flag g) (cons (int g) w)`. -/
def auSetupRecFun : Val → Val
  | .cons (.int g) w => .cons (auSetupFlag g) (.cons (.int g) w)
  | x => x

/-- The cost budget of the setup word, as in the statement of `auSetupRun`. -/
def auSetupBd (p α s t : ℕ) : ℕ := (s + t * auL p α + auCop p α s * s + 1) * (p + 1)

/-- The input array as a list of values. -/
def auSetupInp (u : List (ℤ × ℤ)) : List Val := u.map cfxVal

/-- The extended array of the setup word: `auCop p α s` copies of the input array (as values),
flattened. -/
def auSetupFlat (p α s : ℕ) (u : List (ℤ × ℤ)) : List Val :=
  (List.replicate (auCop p α s) (u.map cfxVal)).flatten

/-- `auSetupFlat` dropped by the offset `auOff p α s`: the `cfxVal`-image of the extended array
`auExt`. -/
def auSetupE (p α s : ℕ) (u : List (ℤ × ℤ)) : List Val := (auSetupFlat p α s u).drop (auOff p α s)

/-- Uniform size bound for one record of the table (the `L` of the `mapList` of the setup word). -/
def auSetupLrec (p α : ℕ) : ℕ := 28 * auL p α * (p + 1)

end Work.Resample
