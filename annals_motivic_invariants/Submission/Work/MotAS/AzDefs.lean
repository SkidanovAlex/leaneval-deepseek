import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.CensusAS2Aux
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The normal form of the forward AS chart component `fwVecAS2 · 0`

Part of the subproject `Submission/Work/MotAS` (`Work.MotAS`, the characteristic-`5`
Artin--Schreier branch of the Crauder--Katz link of Lin--Shinder, *Motivic invariants of
birational maps*).

The zeroth component of the forward chart map of the corrected AS chart is

`f̂₀ = fwVecAS2 a b g 0 = kleinPAS0 (C a) (C b) (C g) (kleinStereoAS (C a) (C b) (pAS0 K) (chart3 K))`

It is a quartic in the three chart coordinates `X₀, X₁, X₂`, and our aim in this chapter is to
prove that it is a *prime* element of `MvPolynomial (Fin 3) (RatFunc 𝕜)`.

This file collects the *normal forms* on which that proof rests, all of them polynomial identities
with integer coefficients (hence valid over any field).

* `fwVecAS2_zero_eq` : `f̂₀ = C A · azQ a b g` where `A = azA a b = a² − ab − b²` (a **unit** as soon
  as `A ≠ 0`, which is part of the `ASGood` hypotheses);

* `azQ_succEquiv` : `azQ` is **quadratic in `X₀`** over `K[X₁,X₂]`, with coefficients
  `azC2, azC1, azC0` (transported along `MvPolynomial.finSuccEquiv K 2`).

Consequently `f̂₀`, being `C A` times `azQ` with `A` a unit, is prime as soon as `azQ` is
irreducible; and irreducibility of the quadratic `azQ` reduces (via the general criterion
`Work.MotAS.azIrreducible_quadratic`) to the two statements `azContent` (the three coefficients have
no common divisor) and `azDisc_not_square` (the discriminant is not a square).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [Field K]

/-! ## §1 The scalar abbreviations -/

/-- `A = a² − ab − b²`, the discriminant of the Klein quadric in the AS chart. -/
def azA (a b : K) : K := a ^ 2 - a * b - b ^ 2

/-- `B = a² + b²`. -/
def azB (a b : K) : K := a ^ 2 + b ^ 2

/-- `D = a² − b²`. -/
def azD (a b : K) : K := a ^ 2 - b ^ 2

/-- `c = −2a² + ab + 2b²`. -/
def azc (a b : K) : K := -2 * a ^ 2 + a * b + 2 * b ^ 2

/-- `E = 2a² + ab − 2b² = c + 4D`, the `X₂`-coefficient of the `X₀`-linear coefficient of `azQ`. -/
def azE (a b : K) : K := 2 * a ^ 2 + a * b - 2 * b ^ 2

/-! ## §2 The normal form of `fwVecAS2 · 0` -/

/-- The AS quadric at the source chart vector `chart3 = (0, X₀, X₁, X₂, 1)`, together with the
`X₀`-part of its polar form at `pAS0`: the Galois coordinate `y₀`. -/
noncomputable def azq (a b : K) : MvPolynomial (Fin 3) K :=
  C (-(2 * azA a b)) * X 0 * X 2 + C (-(azA a b)) * X 1 ^ 2 + C (-(2 * azB a b)) * X 1
    + C (2 * azB a b) * X 2 ^ 2 + C (azc a b)

/-- **The normal form `Q` of the zeroth component of the forward AS chart map**: the quartic such
that `fwVecAS2 a b g 0 = C (azA a b) · azQ a b g`. -/
noncomputable def azQ (a b g : K) : MvPolynomial (Fin 3) K :=
  azq a b ^ 2 - C (4 * azB a b) * azq a b * X 1 + C (4 * azD a b) * azq a b
    + C g * (C (8 * azA a b ^ 2) * X 0 + C (8 * azA a b ^ 2) * X 1 * X 2
        + C (4 * azA a b * azB a b) * X 2)
    + C (4 * azA a b * azB a b) * X 0 ^ 2 + C (4 * azA a b * azB a b) * X 2 ^ 2
    + C (4 * azA a b * azD a b) * X 1 ^ 2 + C (4 * azA a b * azD a b)
    - C (8 * azA a b * azD a b) * X 0 * X 2 - C (8 * azA a b * azB a b) * X 1

/-- The stereographic image of the chart vector is `y₀ = azq`, `yᵢ = 2A·vᵢ` (`i ≥ 1`), because the
polar form of the AS quadric at `pAS0 = e₀` is the constant `−2A·v₄` and `v₄ = 1`. -/
theorem kleinStereoAS_pAS0_chart3 (a b : K) :
    kleinStereoAS (C a) (C b) (pAS0 K) (Work.MotK.chart3 K)
      = fun i => kleinQAS (C a) (C b) (Work.MotK.chart3 K) * (pAS0 K i)
          + C (2 * azA a b) * (Work.MotK.chart3 K i) := by
  funext i
  fin_cases i <;>
    · rw [kleinStereoAS, kleinBilinAS_pAS0]
      simp only [azA, Work.MotK.chart3, pAS0, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, map_sub, map_mul, map_pow, map_add, map_neg, map_ofNat]
      first | refl_ring1 | ring

/-- **The normal form of the zeroth component of the forward AS chart map.** -/
theorem fwVecAS2_zero_eq (a b g : K) :
    fwVecAS2 a b g 0 = C (azA a b) * azQ a b g := by
  rw [fwVecAS2, kleinStereoAS_pAS0_chart3]
  simp only [kleinPAS, kleinPAS0, azQ, azq, azA, azB, azD, azc, kleinQAS, pAS0,
    Work.MotK.chart3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  first | refl_ring1 | ring

/-! ## §3 The `X₀`-quadratic structure -/

/-- The `X₀²`-coefficient of `azQ` in the ring `K[X₁,X₂]`: `4A²X₂² + 4AB`. -/
noncomputable def azC2 (a b : K) : MvPolynomial (Fin 2) K :=
  C (4 * azA a b ^ 2) * X 1 ^ 2 + C (4 * azA a b * azB a b)

/-- The `X₀`-coefficient of `azQ` in the ring `K[X₁,X₂]`:
`4A²X₁²X₂ + 16AB·X₁X₂ − 8AB·X₂³ − 4AE·X₂ + 8A²g`. -/
noncomputable def azC1 (a b g : K) : MvPolynomial (Fin 2) K :=
  C (4 * azA a b ^ 2) * X 0 ^ 2 * X 1 + C (16 * azA a b * azB a b) * X 0 * X 1
    - C (8 * azA a b * azB a b) * X 1 ^ 3 - C (4 * azA a b * azE a b) * X 1
    + C (8 * azA a b ^ 2) * C g

/-- The `X₀⁰`-part of `azq`: `q₀ = −AX₁² − 2B·X₁ + 2B·X₂² + c`. -/
noncomputable def azq0 (a b : K) : MvPolynomial (Fin 2) K :=
  C (-(azA a b)) * X 0 ^ 2 + C (-(2 * azB a b)) * X 0 + C (2 * azB a b) * X 1 ^ 2
    + C (azc a b)

/-- The `X₀⁰`-coefficient of `azQ` in the ring `K[X₁,X₂]`:
`q₀² − 4B·q₀X₁ + 4D·q₀ + 8A²g·X₁X₂ + 4ABg·X₂ + 4AB·X₂² + 4AD·X₁² + 4AD − 8AB·X₁`. -/
noncomputable def azC0 (a b g : K) : MvPolynomial (Fin 2) K :=
  azq0 a b ^ 2 - C (4 * azB a b) * azq0 a b * X 0 + C (4 * azD a b) * azq0 a b
    + C (8 * azA a b ^ 2) * C g * X 0 * X 1 + C (4 * azA a b * azB a b) * C g * X 1
    + C (4 * azA a b * azB a b) * X 1 ^ 2 + C (4 * azA a b * azD a b) * X 0 ^ 2
    + C (4 * azA a b * azD a b) - C (8 * azA a b * azB a b) * X 0

/-- **The discriminant of the quadratic `azQ` in `X₀`**, in the ring `K[X₁,X₂]`:
`azC1² − 4·azC2·azC0`.  Its non-squareness is one of the two inputs of the irreducibility
criterion `Work.MotAS.azIrreducible_quadratic`. -/
noncomputable def azDisc (a b g : K) : MvPolynomial (Fin 2) K :=
  azC1 a b g ^ 2 - 4 * azC2 a b * azC0 a b g

/-- `finSuccEquiv` sends constants to constants. -/
theorem finSuccEquiv_C' (r : K) :
    MvPolynomial.finSuccEquiv K 2 (MvPolynomial.C r)
      = Polynomial.C (MvPolynomial.C r) := by
  rw [← MvPolynomial.algebraMap_eq K (Fin 3), AlgEquiv.commutes, Polynomial.algebraMap_apply]
  rfl

theorem finSuccEquiv_X_1 :
    MvPolynomial.finSuccEquiv K 2 (X 1 : MvPolynomial (Fin 3) K)
      = Polynomial.C (X 0 : MvPolynomial (Fin 2) K) := by
  rw [show (1 : Fin 3) = Fin.succ 0 from rfl, MvPolynomial.finSuccEquiv_X_succ]

theorem finSuccEquiv_X_2 :
    MvPolynomial.finSuccEquiv K 2 (X 2 : MvPolynomial (Fin 3) K)
      = Polynomial.C (X 1 : MvPolynomial (Fin 2) K) := by
  rw [show (2 : Fin 3) = Fin.succ 1 from rfl, MvPolynomial.finSuccEquiv_X_succ]

/-- **The `X₀`-quadratic structure of `azQ`**: `azQ = C azC2 · X² + C azC1 · X + C azC0` in the
chart coordinates, `azQ` being viewed as a polynomial in `X₀` over `K[X₁,X₂]`. -/
theorem azQ_succEquiv (a b g : K) :
    MvPolynomial.finSuccEquiv K 2 (azQ a b g)
      = Polynomial.C (azC2 a b) * Polynomial.X ^ 2
        + Polynomial.C (azC1 a b g) * Polynomial.X + Polynomial.C (azC0 a b g) := by
  simp only [azQ, azq, azC2, azC1, azC0, azq0, azA, azB, azD, azc, azE,
    MvPolynomial.finSuccEquiv_X_zero, finSuccEquiv_X_1, finSuccEquiv_X_2, finSuccEquiv_C',
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat]
  first | refl_ring1 | ring

end Work.MotAS
