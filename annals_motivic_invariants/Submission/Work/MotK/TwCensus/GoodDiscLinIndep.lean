/-
# `1, x, y, x², xy` are linearly independent in the function field of a Weierstrass curve

ROUTE (Mathlib API, see `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`):

* `WeierstrassCurve.Affine.CoordinateRing E = AdjoinRoot E.polynomial` with `E.polynomial` monic
  of degree `2` in `Y` over `A[X]`, so `CoordinateRing.basis E : Basis (Fin 2) A[X] _` with
  `CoordinateRing.basis_zero : basis 0 = 1` and `CoordinateRing.basis_one : basis 1 = mk E Y`
  (i.e. `genY E`); there is also `CoordinateRing.smul_basis_eq_zero`.
* `Work.MotV.genX E = mk E (C X)` and `Work.MotV.genY E = mk E Y`;
  `CoordinateRing.smul E x y : x • y = mk E (C x) * y`.

Given `∑ i, c i • v i = 0` with `c : Fin 5 → A` and `v = ![1, x, y, x², xy]`, rewrite it in the
`A[X]`-basis `{1, y}`: it becomes
`p • 1 + q • genY E = 0` with `p = C (c 0) + C (c 1) * X + C (c 3) * X ^ 2` and
`q = C (c 2) + C (c 4) * X`; apply `CoordinateRing.smul_basis_eq_zero` to get `p = 0`, `q = 0`,
then use that `1, X, X ^ 2` (resp. `1, X`) are `A`-linearly independent in `A[X]`
(`Polynomial.basisMonomial`, or `Polynomial.degree`/`Finsupp` coefficients) to conclude
`c = 0`.  Clearing denominators from the fraction field: `FunctionField E = FractionRing _` and
`IsFractionRing.injective`, or work directly with `v` as elements of `CoordinateRing E` (the
independence there implies independence in the fraction field, `IsLocalization`/`IsFractionRing`
gives injectivity of the structure map).

No hypothesis on `E` (smoothness, characteristic) is needed.
-/
import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK.TwCensus

noncomputable section

/-- The scalar action of the base field `A` on the affine coordinate ring is the scalar action of
the polynomial ring `A[X]` through `Polynomial.C`. -/
lemma smul_eq_C_smul {A : Type} [Field A] (E : WeierstrassCurve A) (a : A)
    (x : CoordinateRing E) : a • x = Polynomial.C a • x := by
  rw [Algebra.smul_def, Algebra.smul_def,
    IsScalarTower.algebraMap_apply A (Polynomial A) (CoordinateRing E)]
  rfl

/-- `1, x, y, x², xy` are linearly independent in the affine coordinate ring `A[E]`. -/
lemma coordRing_linearIndependent {A : Type} [Field A] (E : WeierstrassCurve A) :
    LinearIndependent A ![1, CoordinateRing.mk E (Polynomial.C Polynomial.X),
        CoordinateRing.mk E (Polynomial.X),
        (CoordinateRing.mk E (Polynomial.C Polynomial.X)) ^ 2,
        CoordinateRing.mk E (Polynomial.C Polynomial.X) * CoordinateRing.mk E (Polynomial.X)] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- Rewrite the `A`-linear combination as `p • 1 + q • Y` with `p = c₀ + c₁X + c₃X²`,
  -- `q = c₂ + c₄X`; here `x = mk (C X)` and `y = mk Y` in the coordinate ring.
  have hsum :
      (∑ i, c i • (![1, CoordinateRing.mk E (Polynomial.C Polynomial.X),
        CoordinateRing.mk E (Polynomial.X),
        (CoordinateRing.mk E (Polynomial.C Polynomial.X)) ^ 2,
        CoordinateRing.mk E (Polynomial.C Polynomial.X) *
          CoordinateRing.mk E (Polynomial.X)] : Fin 5 → CoordinateRing E) i)
      = (Polynomial.C (c 0) + Polynomial.C (c 1) * Polynomial.X +
            Polynomial.C (c 3) * Polynomial.X ^ 2) • (1 : CoordinateRing E)
        + (Polynomial.C (c 2) + Polynomial.C (c 4) * Polynomial.X) •
            CoordinateRing.mk E Polynomial.X := by
    simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
    rw [smul_eq_C_smul E (c 0) 1, smul_eq_C_smul E (c 1) _, smul_eq_C_smul E (c 2) _,
      smul_eq_C_smul E (c 3) _, smul_eq_C_smul E (c 4) _]
    simp only [CoordinateRing.smul]
    rw [mul_one, mul_one]
    simp only [← map_mul, ← map_pow, ← map_add]
    congr 1
    simp only [map_add, map_mul, map_pow]
    first | refl_ring1 | ring
  rw [hsum] at hc
  -- Uniqueness of the expression `p · 1 + q · Y` in the coordinate ring gives `p = q = 0`.
  obtain ⟨hp, hq⟩ := CoordinateRing.smul_basis_eq_zero hc
  intro i
  fin_cases i
  · simpa using congrArg (fun r : Polynomial A => r.coeff 0) hp
  · simpa using congrArg (fun r : Polynomial A => r.coeff 1) hp
  · simpa using congrArg (fun r : Polynomial A => r.coeff 0) hq
  · simpa using congrArg (fun r : Polynomial A => r.coeff 2) hp
  · simpa using congrArg (fun r : Polynomial A => r.coeff 1) hq

theorem GoodDiscLinIndep {A : Type} [Field A] (E : WeierstrassCurve A) :
    LinearIndependent A ![1, Work.MotV.genX E, Work.MotV.genY E, (Work.MotV.genX E) ^ 2,
      Work.MotV.genX E * Work.MotV.genY E] := by
  -- Transport the statement along the injective `A`-algebra map `A[E] → A(E)`.
  let f : CoordinateRing E →ₗ[A] FunctionField E :=
    (IsScalarTower.toAlgHom A (CoordinateRing E) (FunctionField E)).toLinearMap
  have hfker : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr (IsFractionRing.injective _ _)
  have hmap := LinearIndependent.map' (coordRing_linearIndependent E) f hfker
  have hv : (⇑f ∘ ![1, CoordinateRing.mk E (Polynomial.C Polynomial.X),
        CoordinateRing.mk E (Polynomial.X),
        (CoordinateRing.mk E (Polynomial.C Polynomial.X)) ^ 2,
        CoordinateRing.mk E (Polynomial.C Polynomial.X) *
          CoordinateRing.mk E (Polynomial.X)])
      = ![1, Work.MotV.genX E, Work.MotV.genY E, (Work.MotV.genX E) ^ 2,
          Work.MotV.genX E * Work.MotV.genY E] := by
    funext i
    fin_cases i <;> simp [f, Work.MotV.genX, Work.MotV.genY]
  rwa [hv] at hmap

end

end Work.MotK.TwCensus
