import Mathlib
import Submission.Work.MotK.TwRule
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The twisted Pfaffian map `kleinTwP` is a quadratic form: expansion at `x + t·y`

`kleinTwP a b h : (Fin 5 → R) → (Fin 5 → R)` is, in each coordinate, a homogeneous polynomial
of degree `2` in the coordinates with integer coefficients, i.e. a quadratic form over any
commutative ring `R`.  Its polarisation (in the sense used throughout the Klein/T-twist files,
cf. `kleinTwBilin`) is

`kleinTwPolarP a b h x y = kleinTwP a b h (x + y) - kleinTwP a b h x - kleinTwP a b h y`,

which is exactly the `dP_x(y)` of `Submission/Work/MotK/TwRule.lean` (the `A`/`B` ruling vectors
of the T-twisted Crauder–Katz link are `dP_c(u₁)`, `dP_c(u₂)` in this sense).

For a quadratic form the binomial expansion

`P(x + t·y) = P(x) + t·(P(x+y) - P(x) - P(y)) + t²·P(y)`

is a polynomial identity with integer coefficients, hence holds over any commutative ring —
no division by `2` and no hypothesis on `t` is needed.  The lemma `KleinTwPAddSmul` below records
this for `kleinTwP`, in the form the link certificates use it.

The proof is the same recipe as `KleinTwI1` / `TwDataMod5.kleinTwP_homog`: reduce to the five
coordinates (`funext` + `fin_cases`), unfold the explicit quadrics `kleinTwP0, …, kleinTwP4` and
the polarisation `kleinTwPolarP`, expand the vector notation `![…]`, and close with `ring`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Work.MotK

theorem KleinTwPAddSmul {R : Type*} [CommRing R] (a b h : R) (x y : Fin 5 → R) (t : R) :
    Work.MotK.kleinTwP a b h (fun i => x i + t * y i)
      = fun k => Work.MotK.kleinTwP a b h x k + t * Work.MotK.kleinTwPolarP a b h x y k
          + t ^ 2 * Work.MotK.kleinTwP a b h y k := by
  funext k
  fin_cases k <;>
    simp only [kleinTwP, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4, kleinTwPolarP,
      Pi.add_apply] <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val] <;>
    first | refl_ring1 | ring

end Work.MotK
