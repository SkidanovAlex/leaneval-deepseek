import Mathlib
import Submission.HvdH.Interfaces

/-!
# Parameters (paper §5.1): the numbers `b, p, α, T, r` and the lists `tᵢ, sᵢ`.

This module fixes the *exact* objects the `Params` area must compute.  The paper uses primes
`q` in `((1-2η)t, (1-η)t]`; here we replace them by the explicit, PNT-free construction of the
lead, based on `F = (d-1)!` and `Q = ∏_{k<d} (2Fk+1)(2Fk-1)`.

`ss` is `s_i = u_0 + F·i` for `i ≤ d'` (matching `t_i = r/2`) and `s_i = 2u_0 - 1 + 2F·j`
(matching `t_i = r`), where `u_0` is the smallest `≥ L` of the form `Q(1 + mF)`.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

/-- `F = (d-1)!`, divisible by every prime `≤ d`. -/
def Ffac : ℕ := (D - 1).factorial

/-- `Q = ∏_{k=1}^{d-1} (2Fk+1)(2Fk-1)`.  Every prime divisor of `F` is `≤ d`, and each factor is
`≡ ±1` mod it, so `Q ≡ (-1)^{d-1} = 1 (mod F)`. -/
def Qall : ℕ :=
  ((List.range (D - 1)).map fun j => (2 * Ffac * (j + 1) + 1) * (2 * Ffac * (j + 1) - 1)).prod

/-- `kr = ⌈kT/d⌉`, so `r = 2^{kr}`. -/
def krpar (n : ℕ) : ℕ := (kTpar n + D - 1) / D

/-- `d' = d·kr - kT ∈ [0,d)`: the number of `t_i` equal to `r/2`. -/
def dpar (n : ℕ) : ℕ := D * krpar n - kTpar n

/-- `L = ⌊(1-2η)·r/2⌋ + 1` with `η = 1/(4d)`; `(1-2η)r/2 = r(2d-1)/(4d)`. -/
def Lpar (n : ℕ) : ℕ := rpar n * (2 * D - 1) / (4 * D) + 1

/-- `u_0 = Q(1 + mF)` is the least number `≥ L` of this form. -/
def upar (n : ℕ) : ℕ :=
  Qall + ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * (Ffac * Qall)

/-- The list `t_1 ≤ … ≤ t_d`: `d'` copies of `r/2` then `d - d'` copies of `r`. -/
def tsPar (n : ℕ) : List ℕ :=
  (List.range D).map fun k => if k < dpar n then rpar n / 2 else rpar n

/-- The list `s_1 ≤ … ≤ s_d` (order does not matter later; ascending is convenient). -/
def ssPar (n : ℕ) : List ℕ :=
  (List.range D).map fun k =>
    if k < dpar n then upar n + Ffac * (k + 1)
    else 2 * upar n - 1 + 2 * Ffac * (k - dpar n + 1)

/-- A round bound `≥ 2^{70 000 000} > Qall`. -/
def KB : ℕ := 2 ^ (2 ^ 40)

/-- The threshold of the area: `n ≥ n₁ = 2^(2^40 · 8d)`.  Written as a single power (rather than
`KB ^ (8d)`) so that the kernel never has to *evaluate* a tower of exponentials. -/
def n1 : ℕ := 2 ^ (2 ^ 40 * 8 * D)

/-- A bound for the *sizes* (not values) of every constant met in the program:
`2 ^ (2^41) + 16` dominates `KB ^ 2 = 2 ^ (2^41)` and all its factors. -/
def KBsz : ℕ := 2 ^ (2 ^ 41) + 16

end Work.Params
