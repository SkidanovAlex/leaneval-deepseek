import Mathlib
import Submission.Work.MotC.C6.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC.C6

open WeierstrassCurve WeierstrassCurve.Affine
open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

variable {L : Type} [Field L] (W : WeierstrassCurve L)

/-- The class of a coefficient polynomial in the affine coordinate ring, as an algebra map. -/
lemma mk_C (r : Polynomial L) : (CoordinateRing.mk W) (Polynomial.C r)
    = algebraMap (Polynomial L) (CoordinateRing W) r := by
  have h := CoordinateRing.smul (W' := W) r (1 : CoordinateRing W)
  simp only [Algebra.smul_def, mul_one] at h
  exact h.symm

/-- Coefficients `c : L` of `L[X]` map into the function field through `L` itself. -/
lemma algebraMap_C_FunctionField (c : L) :
    algebraMap (Polynomial L) (FunctionField W) (Polynomial.C c)
      = algebraMap L (FunctionField W) c := by
  rw [IsScalarTower.algebraMap_apply L (Polynomial L) (FunctionField W) c,
    Polynomial.algebraMap_eq]

/-- The inner variable of `L[X][Y]` maps to `genX` in the function field. -/
lemma algebraMap_X_FunctionField :
    algebraMap (Polynomial L) (FunctionField W) Polynomial.X = genX W := by
  rw [IsScalarTower.algebraMap_apply (Polynomial L) (CoordinateRing W) (FunctionField W),
    ← mk_C (L := L) W Polynomial.X]
  rfl

/-- The composite `L[X][Y] → L[W] → L(W)` on the coefficients `L[X]`. -/
lemma psi_C (r : Polynomial L) :
    ((algebraMap (CoordinateRing W) (FunctionField W)).comp (CoordinateRing.mk W))
        (Polynomial.C r)
      = algebraMap (Polynomial L) (FunctionField W) r := by
  rw [RingHom.comp_apply, mk_C,
    ← IsScalarTower.algebraMap_apply (Polynomial L) (CoordinateRing W) (FunctionField W)]

/-- The composite `L[X][Y] → L[W] → L(W)` sends the outer variable `Y` to `genY`. -/
lemma psi_Y : ((algebraMap (CoordinateRing W) (FunctionField W)).comp (CoordinateRing.mk W))
    (Y : Polynomial (Polynomial L)) = genY W := rfl

/-- The composite `L[X][Y] → L[W] → L(W)` sends the inner variable to `genX`. -/
lemma psi_X : ((algebraMap (CoordinateRing W) (FunctionField W)).comp (CoordinateRing.mk W))
    (Polynomial.C Polynomial.X) = genX W := rfl

/-- The value of the Weierstrass polynomial under `L[X][Y] → L[W] → L(W)`, expanded. -/
lemma psi_polynomial :
    ((algebraMap (CoordinateRing W) (FunctionField W)).comp (CoordinateRing.mk W))
        (WeierstrassCurve.Affine.polynomial W)
      = genY W ^ 2
        + ((algebraMap L (FunctionField W) W.a₁) * genX W + algebraMap L (FunctionField W) W.a₃)
          * genY W
        - (genX W ^ 3 + (algebraMap L (FunctionField W) W.a₂) * genX W ^ 2
            + (algebraMap L (FunctionField W) W.a₄) * genX W
            + algebraMap L (FunctionField W) W.a₆) := by
  simp only [WeierstrassCurve.Affine.polynomial, map_sub, map_add, map_mul, map_pow, psi_C,
    psi_Y, algebraMap_C_FunctionField, algebraMap_X_FunctionField]

/-- The Weierstrass polynomial of `W` dies in the function field. -/
lemma psi_polynomial_eq_zero :
    ((algebraMap (CoordinateRing W) (FunctionField W)).comp (CoordinateRing.mk W))
        (WeierstrassCurve.Affine.polynomial W) = 0 := by
  rw [RingHom.comp_apply, AdjoinRoot.mk_self, map_zero]

/-- **The generic point is a nonsingular point.** For a Weierstrass curve `W` over a field `L` with
`Δ ≠ 0`, the pair `([X], [Y])` of classes of the two coordinate functions in the function field
`K = L(W)` satisfies the Weierstrass equation of `W` base changed to `K`, and is non-singular there
(a point of the equation is non-singular as soon as `Δ ≠ 0`, by
`WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero`).

Route for the equation: in the coordinate ring `L[W] = AdjoinRoot W.polynomial` one has
`AdjoinRoot.mk_self : mk W W.polynomial = 0`, i.e.
`(mk W Y)^2 + mk W (C (C a₁ * X + C a₃)) * mk W Y - mk W (C (X^3 + C a₂ X^2 + C a₄ X + C a₆)) = 0`
(rewrite `WeierstrassCurve.Affine.polynomial`), and `mk W (C p) = algebraMap L[X] (CoordinateRing W) p`
(`WeierstrassCurve.Affine.CoordinateRing.smul` with `y = 1`), so with
`x₀ = mk W (C X) = algebraMap L[X] _ X` and `y₀ = mk W Y` this reads
`y₀^2 + (algebraMap L _ a₁) * x₀ * y₀ + (algebraMap L _ a₃) * y₀ = x₀^3 + ...` in the coordinate
ring; apply `algebraMap (CoordinateRing W) K` and rewrite with
`WeierstrassCurve.Affine.equation_iff`.  The `Δ ≠ 0` hypothesis for `W` base changed to `K` follows
from `WeierstrassCurve.map_Δ`. -/
theorem genX_genY_nonsingular {L : Type} [Field L] (W : WeierstrassCurve L) (hΔ : W.Δ ≠ 0) :
    WeierstrassCurve.Affine.Nonsingular (W.baseChange (WeierstrassCurve.Affine.FunctionField W))
      (Work.MotC.C6.genX W) (Work.MotC.C6.genY W) := by
  have hΔK : (W.baseChange (WeierstrassCurve.Affine.FunctionField W)).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    intro h
    exact hΔ (RingHom.injective (algebraMap L (WeierstrassCurve.Affine.FunctionField W))
      (by rw [h, map_zero]))
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (W := W.baseChange (WeierstrassCurve.Affine.FunctionField W)) hΔK]
  rw [WeierstrassCurve.Affine.equation_iff]
  rw [WeierstrassCurve.Affine.baseChange_a₁, WeierstrassCurve.Affine.baseChange_a₂,
    WeierstrassCurve.Affine.baseChange_a₃, WeierstrassCurve.Affine.baseChange_a₄,
    WeierstrassCurve.Affine.baseChange_a₆]
  have hψ := psi_polynomial_eq_zero W
  rw [psi_polynomial W] at hψ
  linear_combination (norm := first | refl_ring1 | ring1) hψ

end

end Work.MotC.C6
