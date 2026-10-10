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

set_option linter.style.haveILetI false

open WeierstrassCurve
open WeierstrassCurve.Affine

/-- For the affine point `T = (a, b)` of `E` and the coordinates `U = transX E T`, `V = transY E T`
of the translate `genPoint + T` of the generic point, in the chart at infinity
`u = 1/x`, `w = y/x²` one has `(U - a)·(1 - a·u)² = λ·u + κ·u² - μ·w`, where
`μ = 2b + a₁a + a₃`, `λ = 3a² + 2a₂a + a₄ - a₁b`, `κ = a₆ + b² + a₁ab - 2a³ - a₂a²`
(`muCoeff`, `lamCoeff`, `kapCoeff`).

Route: `transX E T = addX (baseE E) (genX E) a ℓ` (`transX_some`) with
`ℓ = slope (baseE E) (genX E) a (genY E) b = (genY E - b)/(genX E - a)`
(`slope_of_X_ne`, `genX_ne_algebraMap`), and `addX W x₁ x₂ ℓ = ℓ^2 + a₁ℓ - a₂ - x₁ - x₂`.
Rewrite `genX E = 1/u` and `genY E = w/u²` (`infU`, `infW`), clear denominators, and close with the
chart relation `infW_sq_relation`. -/
theorem TransXFormula (L : Type*) [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (a b : L) (h : WeierstrassCurve.Affine.Nonsingular E a b) :
    (Work.MotC2.transX E (WeierstrassCurve.Affine.Point.some a b h) -
        algebraMap L (Work.MotC2.Func E) a) *
        (1 - algebraMap L (Work.MotC2.Func E) a * Work.MotC2.infU E) ^ 2 =
      algebraMap L (Work.MotC2.Func E) (Work.MotC2.lamCoeff E a b) * Work.MotC2.infU E +
        algebraMap L (Work.MotC2.Func E) (Work.MotC2.kapCoeff E a b) *
          (Work.MotC2.infU E) ^ 2 -
        algebraMap L (Work.MotC2.Func E) (Work.MotC2.muCoeff E a b) * Work.MotC2.infW E := by
  -- use the same `DecidableEq` instance for the `slope` occurring in `transX`
  letI : DecidableEq (Work.MotC2.Func E) := Work.MotC2.instDecEqFunc E
  have hxne : Work.MotC2.genX E ≠ algebraMap L (Work.MotC2.Func E) a :=
    Work.MotC2.genX_ne_algebraMap E a
  have hrel := Work.MotC2.genX_genY_relation E
  have hxux : Work.MotC2.genX E * Work.MotC2.infU E = 1 := by
    rw [mul_comm]; exact Work.MotC2.infU_mul_genX E
  -- the identity in the affine coordinates `(x, y)`
  have hkey : (Work.MotC2.transX E (WeierstrassCurve.Affine.Point.some a b h) -
        algebraMap L (Work.MotC2.Func E) a) *
        (Work.MotC2.genX E - algebraMap L (Work.MotC2.Func E) a) ^ 2 =
      algebraMap L (Work.MotC2.Func E) (Work.MotC2.lamCoeff E a b) * Work.MotC2.genX E +
        algebraMap L (Work.MotC2.Func E) (Work.MotC2.kapCoeff E a b) -
        algebraMap L (Work.MotC2.Func E) (Work.MotC2.muCoeff E a b) * Work.MotC2.genY E := by
    rw [Work.MotC2.transX_some]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      Work.MotC2.baseE, Work.MotC2.muCoeff, Work.MotC2.lamCoeff, Work.MotC2.kapCoeff,
      map_add, map_sub, map_mul, map_pow, map_ofNat]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hxne]
    field_simp
    linear_combination (norm := first | refl_ring1 | ring1) hrel
  have hw : Work.MotC2.infW E = Work.MotC2.genY E * (Work.MotC2.infU E) ^ 2 := by
    rw [Work.MotC2.infW, Work.MotC2.infU, div_eq_mul_inv, inv_pow]
  have hAu : 1 - algebraMap L (Work.MotC2.Func E) a * Work.MotC2.infU E =
      (Work.MotC2.genX E - algebraMap L (Work.MotC2.Func E) a) * Work.MotC2.infU E := by
    rw [sub_mul, hxux]
  rw [hAu, mul_pow, hw]
  linear_combination (norm := first | refl_ring1 | ring1) (Work.MotC2.infU E) ^ 2 * hkey +
    (algebraMap L (Work.MotC2.Func E) (Work.MotC2.lamCoeff E a b) * Work.MotC2.infU E) * hxux

end Work.MotC2
