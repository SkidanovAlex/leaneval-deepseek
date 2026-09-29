import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWhs

/-!
# `Work.Resample.buQWRdefs`: radius bookkeeping of the Neumann rounds of the `B̃` word

The word `q` of `Work.Resample.buQWrounds` runs the Neumann round `Work.Resample.buQWstep`
`n - 1` times (`n = egN p α s t`), starting from the pair `(v, v)`, and outputs the second
component of the folded state.  Every round is exact integer (fixed point) arithmetic on vectors
of `s` complex pairs:

`v ↦ v' = buRoundL Wt p s m v`,  `acc ↦ acc' = buAddV acc (buSMulV σ v')`,

and this module fixes the *radii* used to keep the two vectors inside the disc:

* `buQWB p α i` bounds the radius of `v` after `i` rounds,
* `buQWB2 p α i` bounds the radius of `acc` after `i` rounds,

with `buQWB p α 0 = buQWB2 p α 0 = 2^(p-1) + 2` (the input hypothesis of
`Work.Resample.buQWrounds`) and the recurrences that `Work.Resample.buQWstep` produces
(its postcondition bounds the outputs by `B/2 + 34m + 4` and `B2 + B/2 + 34m + 5`,
`m = egM p α`).

`Work.Resample.buQWRrad` (delegated) is the resulting arithmetic statement: every `B_i`, `B2_i`
stays below `2^(p+2)` (the side condition of `buQWstep`), and the final radius `B2_{n-1}` is below
`2^(p+1)` (the postcondition of `buQWrounds`).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- Radius bound for the vector `v` after `i` Neumann rounds. -/
def buQWB (p α : ℕ) : ℕ → ℕ
  | 0 => 2 ^ (p - 1) + 2
  | (i + 1) => buQWB p α i / 2 + 34 * egM p α + 4

/-- Radius bound for the accumulator after `i` Neumann rounds. -/
def buQWB2 (p α : ℕ) : ℕ → ℕ
  | 0 => 2 ^ (p - 1) + 2
  | (i + 1) => buQWB2 p α i + buQWB p α i / 2 + 34 * egM p α + 5

theorem buQWB_zero (p α : ℕ) : buQWB p α 0 = 2 ^ (p - 1) + 2 := rfl

theorem buQWB_succ (p α i : ℕ) : buQWB p α (i + 1) = buQWB p α i / 2 + 34 * egM p α + 4 := rfl

theorem buQWB2_zero (p α : ℕ) : buQWB2 p α 0 = 2 ^ (p - 1) + 2 := rfl

theorem buQWB2_succ (p α i : ℕ) :
    buQWB2 p α (i + 1) = buQWB2 p α i + buQWB p α i / 2 + 34 * egM p α + 5 := rfl

end Work.Resample
