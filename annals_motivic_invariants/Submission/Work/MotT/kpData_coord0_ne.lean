import Mathlib
import Submission.Work.MotT.KleinParamData
import Submission.Work.MotK.Spans
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Nonvanishing of the first Klein coordinate of the parametric datum `(u,1)`

This file proves `Work.MotT.kpData_coord0_ne`, the `coord0_ne` field of
`Work.MotV.KleinData.Good` for the parametric Klein datum `kpData K u` of
`Submission/Work/MotT/KleinParamData.lean`.

The first row of the coordinate matrix `kpCoord K u` is

`(-5⁸·u¹⁷·Δ³/W², 5¹⁴·u²¹·(4u⁵+3)·Δ/W, 0, 5¹⁴·u²⁵, 0)`,

so in the function field of `E_u` over any extension `L/K` the first Klein form is the
quadratic polynomial

`κ₀ = c₀ + c₁·x + c₃·x²`

in the `x`-coordinate `x = genX`, whose leading coefficient `c₃ = 5¹⁴·u²⁵` is nonzero as soon
as `u ≠ 0` and `ringChar K ≠ 5`.  Since `x` is transcendental over `L` (the coordinate ring of a
Weierstrass curve is free of rank two over `L[X]`, so a nonzero polynomial in `x` does not
vanish in the function field — `Work.MotK.algebraMap_polynomial_ne_zero`), `κ₀ ≠ 0`.

Note that the hypotheses `hk : ringChar K ≠ 5` and `hu : u ≠ 0` are exactly what is needed:
in characteristic `5` the whole first row of `kpCoord` degenerates to zero.  The hypothesis
`hΔ` is not used.
-/

set_option linter.style.haveILetI false

namespace Work.MotT

open WeierstrassCurve WeierstrassCurve.Affine

/-- In the function field of a Weierstrass curve `W` over a field `L`, a quadratic polynomial
`a + b·x + c·x²` in the `x`-coordinate `x = genX W` with `c ≠ 0` does not vanish. -/
lemma functionField_quad_ne_zero (L : Type) [Field L] (W : WeierstrassCurve L) (a b c : L)
    (hc : c ≠ 0) :
    algebraMap L (Affine.FunctionField W) a * 1
      + algebraMap L (Affine.FunctionField W) b * Work.MotV.genX W
      + algebraMap L (Affine.FunctionField W) c * Work.MotV.genX W ^ 2 ≠ 0 := by
  -- `Polynomial.X` is the `x`-coordinate in the function field
  have hgen : algebraMap (Polynomial L) (Affine.FunctionField W) Polynomial.X
      = Work.MotV.genX W := by
    rw [Work.MotV.genX]
    exact (IsScalarTower.algebraMap_apply (Polynomial L) (CoordinateRing W)
      (Affine.FunctionField W) Polynomial.X).symm
  -- both sides are the image of the same quadratic polynomial
  have hid : algebraMap (Polynomial L) (Affine.FunctionField W)
        (Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2)
      = algebraMap L (Affine.FunctionField W) a * 1
        + algebraMap L (Affine.FunctionField W) b * Work.MotV.genX W
        + algebraMap L (Affine.FunctionField W) c * Work.MotV.genX W ^ 2 := by
    simp only [map_add, map_mul, map_pow, Polynomial.C_eq_algebraMap, hgen,
      IsScalarTower.algebraMap_apply L (Polynomial L) (Affine.FunctionField W)]
    first | refl_ring1 | ring
  rw [← hid]
  -- a nonzero polynomial in `x` does not vanish in the function field; the coefficient of `X²`
  -- is `c ≠ 0`
  refine Work.MotK.algebraMap_polynomial_ne_zero L W _ (fun hP => hc ?_)
  have h := congrArg (fun p : Polynomial L => p.coeff 2) hP
  simpa using h

theorem kpData_coord0_ne (K : Type) [Field K] (hk : ringChar K ≠ 5) (u : K) (hu : u ≠ 0)
    (hΔ : Work.MotT.kpDelta K u ≠ 0) :
    ∀ (L : Type) [Field L] [Algebra K L],
      Work.MotV.kleinCoord (Work.MotT.kpData K u) L 0 ≠ 0 := by
  intro L _ _
  -- `5 ≠ 0` in `K`, since the characteristic is not `5`
  have h5 : (5 : K) ≠ 0 := by
    haveI := ringChar.charP K
    exact CharP.cast_ne_zero_of_ne_of_prime (R := K) Nat.prime_five hk
  -- the coefficient of `X²` in `κ₀`, i.e. the entry `(0,3)` of the coordinate matrix
  have h3 : (Work.MotT.kpCoord K u) 0 3 ≠ 0 := by
    have h : (Work.MotT.kpCoord K u) 0 3 = 6103515625 * u ^ 25 := by
      simp [Work.MotT.kpCoord]
    rw [h]
    refine mul_ne_zero ?_ (pow_ne_zero 25 hu)
    have h610 : (6103515625 : K) = (5 : K) ^ 14 := by norm_num
    rw [h610]
    exact pow_ne_zero 14 h5
  have h3L : algebraMap K L ((Work.MotT.kpCoord K u) 0 3) ≠ 0 := fun h =>
    h3 ((algebraMap K L).injective (by rw [h, map_zero]))
  -- the two remaining entries of the first row vanish
  have hp2 : (Work.MotT.kpCoord K u) 0 2 = (0 : K) := by simp [Work.MotT.kpCoord]
  have hp4 : (Work.MotT.kpCoord K u) 0 4 = (0 : K) := by simp [Work.MotT.kpCoord]
  -- `κ₀` is the quadratic polynomial `c₀ + c₁·x + c₃·x²`
  have hid : Work.MotV.kleinCoord (Work.MotT.kpData K u) L 0 =
      algebraMap L (Affine.FunctionField ((Work.MotT.kpData K u).E.baseChange L))
          (algebraMap K L ((Work.MotT.kpCoord K u) 0 0)) * 1
      + algebraMap L (Affine.FunctionField ((Work.MotT.kpData K u).E.baseChange L))
          (algebraMap K L ((Work.MotT.kpCoord K u) 0 1)) *
        Work.MotV.genX ((Work.MotT.kpData K u).E.baseChange L)
      + algebraMap L (Affine.FunctionField ((Work.MotT.kpData K u).E.baseChange L))
          (algebraMap K L ((Work.MotT.kpCoord K u) 0 3)) *
        Work.MotV.genX ((Work.MotT.kpData K u).E.baseChange L) ^ 2 := by
    rw [Work.MotV.kleinCoord_eq_sum, Fin.sum_univ_five]
    simp only [Work.MotT.kpData_coord, Work.MotV.kleinBas]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    rw [hp2, hp4]
    simp only [map_zero, zero_mul, add_zero, mul_one]
  rw [hid]
  exact functionField_quad_ne_zero L ((Work.MotT.kpData K u).E.baseChange L) _ _ _ h3L

end Work.MotT
