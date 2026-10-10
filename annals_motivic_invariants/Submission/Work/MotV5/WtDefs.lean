import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Route V, characteristic 5: the weighted-polynomial layer of `tp_as`

`Work.MotV5.polyOf y` is the polynomial `∑ y_j T^j` attached to the AS Galois coordinates of
`tp_as`, and `kleinQPoly a b P` is the Klein polynomial
`-ab P(T)² + a² P(T+2)P(T+3) - b² P(T+1)P(T+4)` of `P`.

The point of these definitions is that the hypothesis `heq` of `tp_as` is equivalent to the
divisibility `(T⁵ - T - g) ∣ kleinQPoly a b (polyOf y)` in `F[T]` (see `dvd_kleinQ`), and the
latter is a purely polynomial statement, to which the weighted leading-term argument
(`wt`, `Wt`, …) applies.
-/

set_option autoImplicit false

namespace Work.MotV5

open Polynomial

/-- The Klein polynomial `-ab P(T)² + a² P(T+2)P(T+3) - b² P(T+1)P(T+4)` of `P`. -/
noncomputable def kleinQPoly {F : Type*} [CommRing F] (a b : F) (P : Polynomial F) :
    Polynomial F :=
  -C (a * b) * P ^ 2
    + C (a ^ 2) * (P.comp (X + C 2)) * (P.comp (X + C 3))
    - C (b ^ 2) * (P.comp (X + C 1)) * (P.comp (X + C 4))

/-- The polynomial `∑_{j<5} y_j T^j` attached to a vector `y`. -/
noncomputable def polyOf {F : Type*} [CommRing F] (y : Fin 5 → F) : Polynomial F :=
  ∑ j : Fin 5, C (y j) * X ^ (j : ℕ)

/-- The Artin–Schreier polynomial `T⁵ - T - g`. -/
noncomputable def asPolyF {F : Type*} [CommRing F] (g : F) : Polynomial F := X ^ 5 - X - C g

/-- The weight of the monomial `c T^l`: `(v g)^l * (v c)^5`.  The fifth power is what makes the
weight multiplicative (`wt_mul`), which is the reason for using it instead of a fifth root of
`v g` (which need not exist in the value group). -/
noncomputable def wt {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (g : F) (c : F) (l : ℕ) : Γ₀ := (v g) ^ l * (v c) ^ 5

theorem wt_mul {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (g : F) (c d : F) (l m : ℕ) :
    wt v g (c * d) (l + m) = wt v g c l * wt v g d m := by
  simp only [wt, map_mul, pow_add, mul_pow, mul_assoc, mul_left_comm, mul_comm]

theorem wt_zero {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (g c : F) (l : ℕ) (hc : c = 0) : wt v g c l = 0 := by
  subst hc; simp [wt]

/-- The `Γ₀`-valued "sup of the weights of the monomials" of `f`. -/
noncomputable def Wt {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (g : F) (f : Polynomial F) : Γ₀ :=
  f.support.sup (fun l => wt v g (f.coeff l) l)

/-- The "top part" of `f`: the sum of its monomials of maximal weight. -/
noncomputable def topPart {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (g : F) (f : Polynomial F) : Polynomial F :=
  ∑ l ∈ f.support, if wt v g (f.coeff l) l = Wt v g f then C (f.coeff l) * X ^ l else 0

end Work.MotV5
