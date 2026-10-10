import Mathlib
import Submission.Work.MotK.TwRule

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Functoriality of the twisted Pfaffian map under a change of coefficients

Each component `kleinTwPk a b h x` (`k = 0,…,4`) of the twisted Pfaffian map
`kleinTwP a b h x = ![kleinTwP0 …, …, kleinTwP4 …]` is a polynomial with integer
coefficients in the entries `a`, `b`, `h` and `x 0, …, x 4`: it is built from those
variables using only `+`, `-`, `*`, `^` and the integer literal `2`.  Hence it commutes
with every ring homomorphism `φ`: pushing `φ` inside component by component (via `map_add`,
`map_sub`, `map_mul`, `map_pow`, `map_neg`) and evaluating the five entries of the vector
notation gives the same expression with `a`, `b`, `h`, `x i` replaced by their images.

This is the `map`-twisted analogue of the functoriality of the underlying Klein data, and
is needed to transport the twisted Crauder–Katz link along a change of base ring/field.
-/

namespace Work.MotK

theorem KleinTwPMapApply {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b h : R)
    (x : Fin 5 → R) (k : Fin 5) :
    φ (Work.MotK.kleinTwP a b h x k)
      = Work.MotK.kleinTwP (φ a) (φ b) (φ h) (fun i => φ (x i)) k := by
  fin_cases k <;>
    simp [Work.MotK.kleinTwP, Work.MotK.kleinTwP0, Work.MotK.kleinTwP1, Work.MotK.kleinTwP2,
      Work.MotK.kleinTwP3, Work.MotK.kleinTwP4, map_add, map_sub, map_mul, map_pow, map_neg]

end Work.MotK
