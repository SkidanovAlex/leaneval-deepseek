import Mathlib
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.TransPlaceCoeffs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open WeierstrassCurve
open WeierstrassCurve.Affine

-- `transX`/`transY` were defined using the `DecidableEq` instance on the function field that
-- `TranslationDefs` installs locally; we re-register exactly that instance so that `slope` terms we
-- write are syntactically the ones produced by `transY_some`.
attribute [local instance] Work.MotC2.instDecEqFunc

/-- The algebraic heart of `TransYFormula`, stripped of all curve-theoretic structure.

Let `R` be a commutative ring and let `(x, y)` satisfy the Weierstrass equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`, while `(a, b)` lies on the line of slope `l` through
`(x, y)`, i.e. `y - b = l(x - a)`.  Write `μ = 2b + a₁a + a₃`, `λ = 3a² + 2a₂a + a₄ - a₁b`,
`κ = a₆ + b² + a₁ab - 2a³ - a₂a²`, and let `V` be the `Y`-coordinate of the subtraction of the
third intersection point of that line with the curve, computed by the secant formula
`V = -(l(A - x) + y) - a₁A - a₃` with `A = l² + a₁l - a₂ - x - a`.  Then
`(V - b)(x - a)³` is the explicit polynomial in `x, y` displayed below; multiplying by `u³` with
`u = x⁻¹` and using `w = y/x²` yields the chart-at-infinity formula of `TransYFormula`.

Only the Weierstrass equation of `(x, y)` (not of `(a, b)`) enters. -/
theorem transY_ring_id (R : Type*) [CommRing R] (x y a b l A1 A2 A3 A4 A6 : R)
    (hx : y ^ 2 + A1 * x * y + A3 * y = x ^ 3 + A2 * x ^ 2 + A4 * x + A6)
    (hy : y - b = l * (x - a)) :
    ((-(l * ((l ^ 2 + A1 * l - A2 - x - a) - x) + y) - A1 * (l ^ 2 + A1 * l - A2 - x - a) - A3)
        - b) * (x - a) ^ 3 =
      (3 * a * (2 * b + A1 * a + A3) - A1 * (3 * a ^ 2 + 2 * A2 * a + A4 - A1 * b)
          + (2 * b + A1 * a + A3) * A2) * x ^ 2
      + (b * (3 * a ^ 2 + 2 * A2 * a + A4 - A1 * b) + (2 * b + A1 * a + A3) * A4
          + A1 * a * (3 * a ^ 2 + 2 * A2 * a + A4 - A1 * b)
          - A1 * (A6 + b ^ 2 + A1 * a * b - 2 * a ^ 3 - A2 * a ^ 2)
          - 3 * a ^ 2 * (2 * b + A1 * a + A3)) * x
      + ((2 * b + A1 * a + A3) * A6 + b * (A6 + b ^ 2 + A1 * a * b - 2 * a ^ 3 - A2 * a ^ 2)
          + A1 * a * (A6 + b ^ 2 + A1 * a * b - 2 * a ^ 3 - A2 * a ^ 2)
          + a ^ 3 * (2 * b + A1 * a + A3))
      - (3 * a ^ 2 + 2 * A2 * a + A4 - A1 * b) * x * y
      - ((A6 + b ^ 2 + A1 * a * b - 2 * a ^ 3 - A2 * a ^ 2) + (2 * b + A1 * a + A3) * A3
          + (2 * b + A1 * a + A3) * b + A1 * a * (2 * b + A1 * a + A3)) * y := by
  linear_combination (norm := first | refl_ring1 | ring1) (2 * A1 * a - A1 * x + A3 + a * l + 2 * b - l * x) * hx
    + (A1 ^ 2 * a ^ 2 - 2 * A1 ^ 2 * a * x + A1 ^ 2 * x ^ 2 + 2 * A1 * a ^ 2 * l + 2 * A1 * a * b
        - 4 * A1 * a * l * x - 2 * A1 * a * y - 2 * A1 * b * x + 2 * A1 * l * x ^ 2 + A1 * x * y
        - A2 * a ^ 2 + 2 * A2 * a * x - A3 * y + A4 * x + A6 - a ^ 3 + a ^ 2 * l ^ 2 + a * b * l
        - 2 * a * l ^ 2 * x - a * l * y + 3 * a * x ^ 2 + b ^ 2 - b * l * x - 2 * b * y + l ^ 2 * x ^ 2
        + l * x * y - x ^ 3) * hy

/-- For the affine point `T = (a, b)` of `E` and `V = transY E T` (the `Y`-coordinate of the
translate `genPoint + T` of the generic point), in the chart at infinity `u = 1/x`, `w = y/x²`:

`(V - b)·(1 - a·u)³ = (3aμ - a₁λ + μa₂)·u + (bλ + μa₄ + a₁aλ - a₁κ - 3a²μ)·u²
   + (μa₆ + bκ + a₁aκ + a³μ)·u³ - λ·w - (κ + μa₃ + μb + a₁aμ)·u·w`,

where `μ = 2b + a₁a + a₃`, `λ = 3a² + 2a₂a + a₄ - a₁b`, `κ = a₆ + b² + a₁ab - 2a³ - a₂a²`
(`muCoeff`, `lamCoeff`, `kapCoeff`).

Route: `transY E T = addY (baseE E) (genX E) a (genY E) ℓ` (`transY_some`) with
`ℓ = slope (baseE E) (genX E) a (genY E) b = (genY E - b)/(genX E - a)`
(`slope_of_X_ne`, `genX_ne_algebraMap`), and
`addY W x₁ x₂ y₁ ℓ = -(ℓ * (addX W x₁ x₂ ℓ - x₁) + y₁) - W.a₁ * addX W x₁ x₂ ℓ - W.a₃`
(`addX = ℓ^2 + a₁ℓ - a₂ - x₁ - x₂`).  Rewrite `genX E = 1/u`, `genY E = w/u²` (`infU`, `infW`),
clear denominators, and close with the chart relation `infW_sq_relation`. -/
theorem TransYFormula (L : Type*) [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (a b : L) (h : WeierstrassCurve.Affine.Nonsingular E a b) :
    (Work.MotC2.transY E (WeierstrassCurve.Affine.Point.some a b h) -
        algebraMap L (Work.MotC2.Func E) b) *
        (1 - algebraMap L (Work.MotC2.Func E) a * Work.MotC2.infU E) ^ 3 =
      algebraMap L (Work.MotC2.Func E)
          (3 * a * Work.MotC2.muCoeff E a b - E.a₁ * Work.MotC2.lamCoeff E a b
            + Work.MotC2.muCoeff E a b * E.a₂) * Work.MotC2.infU E
      + algebraMap L (Work.MotC2.Func E)
          (b * Work.MotC2.lamCoeff E a b + Work.MotC2.muCoeff E a b * E.a₄
            + E.a₁ * a * Work.MotC2.lamCoeff E a b - E.a₁ * Work.MotC2.kapCoeff E a b
            - 3 * a ^ 2 * Work.MotC2.muCoeff E a b) * (Work.MotC2.infU E) ^ 2
      + algebraMap L (Work.MotC2.Func E)
          (Work.MotC2.muCoeff E a b * E.a₆ + b * Work.MotC2.kapCoeff E a b
            + E.a₁ * a * Work.MotC2.kapCoeff E a b
            + a ^ 3 * Work.MotC2.muCoeff E a b) * (Work.MotC2.infU E) ^ 3
      - algebraMap L (Work.MotC2.Func E) (Work.MotC2.lamCoeff E a b) * Work.MotC2.infW E
      - algebraMap L (Work.MotC2.Func E)
          (Work.MotC2.kapCoeff E a b + Work.MotC2.muCoeff E a b * E.a₃
            + Work.MotC2.muCoeff E a b * b + E.a₁ * a * Work.MotC2.muCoeff E a b) *
          Work.MotC2.infU E * Work.MotC2.infW E := by
  -- The "cleared denominators" form: an identity in `x = genX E`, `y = genY E`.
  have hmain :
      (Work.MotC2.transY E (WeierstrassCurve.Affine.Point.some a b h) -
          algebraMap L (Work.MotC2.Func E) b) *
          (Work.MotC2.genX E - algebraMap L (Work.MotC2.Func E) a) ^ 3 =
        algebraMap L (Work.MotC2.Func E)
            (3 * a * Work.MotC2.muCoeff E a b - E.a₁ * Work.MotC2.lamCoeff E a b
              + Work.MotC2.muCoeff E a b * E.a₂) * (Work.MotC2.genX E) ^ 2
        + algebraMap L (Work.MotC2.Func E)
            (b * Work.MotC2.lamCoeff E a b + Work.MotC2.muCoeff E a b * E.a₄
              + E.a₁ * a * Work.MotC2.lamCoeff E a b - E.a₁ * Work.MotC2.kapCoeff E a b
              - 3 * a ^ 2 * Work.MotC2.muCoeff E a b) * (Work.MotC2.genX E)
        + algebraMap L (Work.MotC2.Func E)
            (Work.MotC2.muCoeff E a b * E.a₆ + b * Work.MotC2.kapCoeff E a b
              + E.a₁ * a * Work.MotC2.kapCoeff E a b
              + a ^ 3 * Work.MotC2.muCoeff E a b)
        - algebraMap L (Work.MotC2.Func E) (Work.MotC2.lamCoeff E a b) *
            (Work.MotC2.genX E) * (Work.MotC2.genY E)
        - algebraMap L (Work.MotC2.Func E)
            (Work.MotC2.kapCoeff E a b + Work.MotC2.muCoeff E a b * E.a₃
              + Work.MotC2.muCoeff E a b * b + E.a₁ * a * Work.MotC2.muCoeff E a b) *
            (Work.MotC2.genY E) := by
    -- `ℓ = (y - b)/(x - a)` satisfies the chord relation.
    have hy : Work.MotC2.genY E - algebraMap L (Work.MotC2.Func E) b =
        WeierstrassCurve.Affine.slope (Work.MotC2.baseE E) (Work.MotC2.genX E)
            (algebraMap L (Work.MotC2.Func E) a) (Work.MotC2.genY E)
            (algebraMap L (Work.MotC2.Func E) b) *
          (Work.MotC2.genX E - algebraMap L (Work.MotC2.Func E) a) := by
      rw [WeierstrassCurve.Affine.slope_of_X_ne (Work.MotC2.genX_ne_algebraMap E a)]
      exact (div_mul_cancel₀ _
        (sub_ne_zero.mpr (Work.MotC2.genX_ne_algebraMap E a))).symm
    -- `transY` unfolded into the addition formula.
    have hV : Work.MotC2.transY E (WeierstrassCurve.Affine.Point.some a b h) =
        -(WeierstrassCurve.Affine.slope (Work.MotC2.baseE E) (Work.MotC2.genX E)
            (algebraMap L (Work.MotC2.Func E) a) (Work.MotC2.genY E)
            (algebraMap L (Work.MotC2.Func E) b) *
          ((WeierstrassCurve.Affine.slope (Work.MotC2.baseE E) (Work.MotC2.genX E)
              (algebraMap L (Work.MotC2.Func E) a) (Work.MotC2.genY E)
              (algebraMap L (Work.MotC2.Func E) b) ^ 2
            + algebraMap L (Work.MotC2.Func E) E.a₁ *
                WeierstrassCurve.Affine.slope (Work.MotC2.baseE E) (Work.MotC2.genX E)
                  (algebraMap L (Work.MotC2.Func E) a) (Work.MotC2.genY E)
                  (algebraMap L (Work.MotC2.Func E) b)
            - algebraMap L (Work.MotC2.Func E) E.a₂ - Work.MotC2.genX E
            - algebraMap L (Work.MotC2.Func E) a) - Work.MotC2.genX E) + Work.MotC2.genY E)
          - algebraMap L (Work.MotC2.Func E) E.a₁ *
              (WeierstrassCurve.Affine.slope (Work.MotC2.baseE E) (Work.MotC2.genX E)
                (algebraMap L (Work.MotC2.Func E) a) (Work.MotC2.genY E)
                (algebraMap L (Work.MotC2.Func E) b) ^ 2
              + algebraMap L (Work.MotC2.Func E) E.a₁ *
                  WeierstrassCurve.Affine.slope (Work.MotC2.baseE E) (Work.MotC2.genX E)
                    (algebraMap L (Work.MotC2.Func E) a) (Work.MotC2.genY E)
                    (algebraMap L (Work.MotC2.Func E) b)
              - algebraMap L (Work.MotC2.Func E) E.a₂ - Work.MotC2.genX E
              - algebraMap L (Work.MotC2.Func E) a)
          - algebraMap L (Work.MotC2.Func E) E.a₃ := by
      rw [Work.MotC2.transY_some]
      simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, Work.MotC2.baseE,
        WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃]
    have hx : Work.MotC2.genY E ^ 2 +
          algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E * Work.MotC2.genY E
          + algebraMap L (Work.MotC2.Func E) E.a₃ * Work.MotC2.genY E
        = Work.MotC2.genX E ^ 3 + algebraMap L (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E ^ 2
          + algebraMap L (Work.MotC2.Func E) E.a₄ * Work.MotC2.genX E
          + algebraMap L (Work.MotC2.Func E) E.a₆ := Work.MotC2.genY_sq_relation E
    have key := transY_ring_id (Work.MotC2.Func E) (Work.MotC2.genX E) (Work.MotC2.genY E)
        (algebraMap L (Work.MotC2.Func E) a) (algebraMap L (Work.MotC2.Func E) b)
        (WeierstrassCurve.Affine.slope (Work.MotC2.baseE E) (Work.MotC2.genX E)
            (algebraMap L (Work.MotC2.Func E) a) (Work.MotC2.genY E)
            (algebraMap L (Work.MotC2.Func E) b))
        (algebraMap L (Work.MotC2.Func E) E.a₁) (algebraMap L (Work.MotC2.Func E) E.a₂)
        (algebraMap L (Work.MotC2.Func E) E.a₃) (algebraMap L (Work.MotC2.Func E) E.a₄)
        (algebraMap L (Work.MotC2.Func E) E.a₆) hx hy
    rw [← hV] at key
    rw [key]
    simp only [Work.MotC2.muCoeff, Work.MotC2.lamCoeff, Work.MotC2.kapCoeff, map_add, map_sub,
      map_mul, map_ofNat, map_pow]
  -- Multiply `hmain` by `u³` and rewrite `u = 1/x`, `w = y/x²`.
  rw [show (1 : Work.MotC2.Func E) - algebraMap L (Work.MotC2.Func E) a * Work.MotC2.infU E
        = (Work.MotC2.genX E - algebraMap L (Work.MotC2.Func E) a) * Work.MotC2.infU E from by
      rw [sub_mul, mul_comm (Work.MotC2.genX E) (Work.MotC2.infU E), Work.MotC2.infU_mul_genX E],
    mul_pow, ← mul_assoc, hmain]
  rw [Work.MotC2.infU, Work.MotC2.infW]
  field_simp [Work.MotC2.genX_ne_zero E]

end Work.MotC2
