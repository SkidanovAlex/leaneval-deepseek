import Mathlib
import Submission.Work.MotAS.WitPt
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.witPfaff`

The five Pfaffians `kleinPASm a b g k` of the AS Klein curve vanish modulo `X^5 - X - g`
at the witness point `witPt a b`: an explicit polynomial identity in `K[X]` with
`K` a field of characteristic `5`.

The proof pushes `MvPolynomial.aeval (witPt a b)` through the (quadratic) definitions of the
Pfaffians (`map_add`, `map_sub`, `map_mul`, `map_pow`, `MvPolynomial.aeval_X`,
`MvPolynomial.aeval_C`), unfolds the witness point and the explicit cofactors `witHk`, pushes
`Polynomial.C` inside (`map_add`, ..., applied to the ring hom `Polynomial.C`), and then
normalises each side with `ring_nf`, reducing the (integer) coefficients modulo `5` with
`reduce_mod_char!` (which reads the `CharP K 5` instance from the context).  Iterating
`ring_nf`/`reduce_mod_char!` a few times makes the two sides literally identical.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.MotAS
open MvPolynomial Polynomial

theorem witPfaff (K : Type) [Field K] [CharP K 5] (a b g : K) (k : Fin 5) :
    MvPolynomial.aeval (Work.MotAS.witPt a b) (Work.MotAS.kleinPASm a b g k)
      = (Polynomial.X^5 - Polynomial.X - Polynomial.C g) * Work.MotAS.witHk k a b g := by
  fin_cases k <;>
  · simp only [kleinPASm, kleinPAS]
    norm_num
    simp only [kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
      map_add, map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    simp only [witPt]
    norm_num
    simp only [witHk]
    norm_num
    simp only [Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow,
      Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
    all_goals refl_ring1 (mod := 5)

end Work.MotAS
