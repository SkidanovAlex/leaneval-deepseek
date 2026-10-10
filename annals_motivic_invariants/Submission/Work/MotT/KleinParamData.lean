import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The parametric Klein datum `(a,b) = (u,1)`: explicit data

This module records the **explicit** Weierstrass model `E_u` and the coordinate matrix
`coord_u` of the Klein data with Klein parameters `a = u`, `b = 1`, i.e. the Klein curve
`C_{u,1} = V(p_0,…,p_4)`, over an arbitrary field `K`.

The data were computed from the flex `(0 : 1 : u⁻¹ : -u⁻¹ : -1)` of `C_{u,1}`: the
hyperosculating form is
`ℓ = (u¹⁰+14u⁵-1)x₀ + 5u²(2u⁵-1)(x₁+x₄) + 5u³(u⁵+2)(x₂+x₃)`,
the Weierstrass coordinates `X ∈ L(2P)`, `Y ∈ L(3P)` are the elements of `L(5P) = ⟨x_i/ℓ⟩`
with pole orders exactly 2, 3, and `coord_u` expresses `κ_i = x_i/ℓ` in the basis
`1, X, Y, X², X·Y` of `L(5P)`.

Abbreviations used below (`U = u`):
```
Δ = U^10 - 11*U^5 - 1        (the discriminant; the family is smooth away from U*Δ = 0)
w = 2*U^5 - 1
```
The model is `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` with
```
a₁ = -(3U⁵+1)/(5U²)
a₂ = -(29U¹⁵+59U¹⁰+63U⁵-3)/(125U⁴w)
a₃ = Δ²/(625U⁶w)
a₄ = Δ²(27U¹⁰+28U⁵-2)/(15625U⁸w²)
a₆ = -(7U⁵-1)Δ⁴/(1953125U¹²w³)
```
Its `j`-invariant is `c₄³/D⁵` with
`D = UΔ` and `c₄ = a^20 + 228a^15b^5 + 494a^10b^10 - 228a^5b^15 + b^20` (`a = u`, `b = 1`),
matching Fisher, *Invariant theory for the elliptic normal quintic I* (the Hesse family is the
universal family over `X(5)`).

All identities stated in the companion files are polynomial identities in `U` and in the
function-field coordinates, verified symbolically (sympy, exact rational arithmetic).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.MotT
noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

variable (K : Type) [Field K]

/-- `Δ = u¹⁰ - 11u⁵ - 1`, the discriminant of the Klein family `(u,1)`. -/
def kpDelta (u : K) : K := u ^ 10 - 11 * u ^ 5 - 1

/-- `w = 2u⁵ - 1`. -/
def kpW (u : K) : K := 2 * u ^ 5 - 1

/-- The first Weierstrass coefficient. -/
def kpA1 (u : K) : K := -(3 * u ^ 5 + 1) / (5 * u ^ 2)

/-- The second Weierstrass coefficient. -/
def kpA2 (u : K) : K :=
  -(29 * u ^ 15 + 59 * u ^ 10 + 63 * u ^ 5 - 3) / (125 * u ^ 4 * kpW K u)

/-- The third Weierstrass coefficient. -/
def kpA3 (u : K) : K := (kpDelta K u) ^ 2 / (625 * u ^ 6 * kpW K u)

/-- The fourth Weierstrass coefficient. -/
def kpA4 (u : K) : K :=
  (kpDelta K u) ^ 2 * (27 * u ^ 10 + 28 * u ^ 5 - 2) / (15625 * u ^ 8 * (kpW K u) ^ 2)

/-- The sixth Weierstrass coefficient. -/
def kpA6 (u : K) : K :=
  -(7 * u ^ 5 - 1) * (kpDelta K u) ^ 4 / (1953125 * u ^ 12 * (kpW K u) ^ 3)

/-- The Weierstrass model `E_u` of `C_{u,1}` attached to the flex `(0:1:u⁻¹:-u⁻¹:-1)`. -/
def kpE (u : K) : WeierstrassCurve K :=
  ⟨kpA1 K u, kpA2 K u, kpA3 K u, kpA4 K u, kpA6 K u⟩

@[simp] lemma kpE_a1 (u : K) : (kpE K u).a₁ = kpA1 K u := rfl
@[simp] lemma kpE_a2 (u : K) : (kpE K u).a₂ = kpA2 K u := rfl
@[simp] lemma kpE_a3 (u : K) : (kpE K u).a₃ = kpA3 K u := rfl
@[simp] lemma kpE_a4 (u : K) : (kpE K u).a₄ = kpA4 K u := rfl
@[simp] lemma kpE_a6 (u : K) : (kpE K u).a₆ = kpA6 K u := rfl

/-- The coordinate matrix: `κ_i = Σ_m coord i m · b_m` with `b = (1, X, Y, X², X·Y)`. -/
def kpCoord (u : K) : Fin 5 → Fin 5 → K :=
  ![![ -390625 * u ^ 17 * (kpDelta K u) ^ 3 / (kpW K u) ^ 2,
       48828125 * u ^ 21 * (4 * u ^ 5 + 3) * kpDelta K u / kpW K u,
       0,
       6103515625 * u ^ 25,
       0],
    ![ 78125 * u ^ 15 * (3 * u ^ 5 + 1) * (kpDelta K u) ^ 3 / (kpW K u) ^ 2,
       19531250 * u ^ 19 * (kpDelta K u) ^ 2 / kpW K u,
       -48828125 * u ^ 21 * (3 * u ^ 5 - 4) * kpDelta K u / kpW K u,
       -1220703125 * u ^ 23 * (u ^ 5 + 2),
       6103515625 * u ^ 25],
    ![ 390625 * u ^ 19 * (kpDelta K u) ^ 3 / (kpW K u) ^ 2,
       -9765625 * u ^ 18 * (6 * u ^ 10 + 24 * u ^ 5 - 1) * kpDelta K u / kpW K u,
       48828125 * u ^ 20 * (7 * u ^ 5 - 1) * kpDelta K u / kpW K u,
       -1220703125 * u ^ 22 * (3 * u ^ 5 + 1),
       6103515625 * u ^ 24],
    ![ -78125 * u ^ 14 * (kpDelta K u) ^ 3 / kpW K u,
       9765625 * u ^ 18 * (7 * u ^ 5 - 1) * kpDelta K u,
       -48828125 * u ^ 20 * (7 * u ^ 5 - 1) * kpDelta K u / kpW K u,
       0,
       -6103515625 * u ^ 24],
    ![ 234375 * u ^ 15 * (kpDelta K u) ^ 3 / kpW K u,
       -9765625 * u ^ 19 * (4 * u ^ 5 + 3) * kpDelta K u,
       48828125 * u ^ 21 * (3 * u ^ 5 - 4) * kpDelta K u / kpW K u,
       1220703125 * u ^ 23 * kpW K u,
       -6103515625 * u ^ 25]]

/-- **The parametric Klein datum** with Klein parameters `(a,b) = (u,1)`. -/
def kpData (u : K) : Work.MotV.KleinData K where
  a := u
  b := 1
  E := kpE K u
  coord := kpCoord K u

@[simp] lemma kpData_a (u : K) : (kpData K u).a = u := rfl
@[simp] lemma kpData_b (u : K) : (kpData K u).b = 1 := rfl
@[simp] lemma kpData_E (u : K) : (kpData K u).E = kpE K u := rfl
@[simp] lemma kpData_coord (u : K) : (kpData K u).coord = kpCoord K u := rfl

end
end Work.MotT
