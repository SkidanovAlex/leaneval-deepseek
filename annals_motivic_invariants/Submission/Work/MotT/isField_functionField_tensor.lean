import Mathlib

set_option linter.unusedVariables false -- v435-speed

/-!
# Base change of the function field of a Weierstrass curve

For a Weierstrass curve `W` over a field `L` with `W.Δ ≠ 0` and an algebraic field extension
`Ω/L`, the base change `L(W) ⊗_L Ω` of the function field of `W` is a field, i.e. `L(W)` is
linearly disjoint from `Ω` over `L` (regularity of the function field of a smooth curve).

The proof goes through the affine coordinate ring `L[W] = L[X, Y]/⟨W(X,Y)⟩`:

* `Ω ⊗[L] L[W] ≅ Ω[W.baseChange Ω] = Ω[X, Y]/⟨W_Ω(X,Y)⟩` (base change of `AdjoinRoot`), and the
  latter is an integral domain because the Weierstrass polynomial is monic of `Y`-degree two and
  irreducible over any domain (`CoordinateRing.instIsDomain`, from `irreducible_polynomial`);
* `L(W) ⊗[L] Ω = Frac(L[W]) ⊗[L] Ω` is the localisation of the domain `Ω ⊗[L] L[W]` at the image
  of the non-zero elements of `L[W]` (`IsLocalization.tensorProduct_tensorProduct_right`), hence a
  domain;
* a domain which is algebraic (in particular integral) over a subfield is a field
  (`Algebra.TensorProduct.isField_of_isAlgebraic`).
-/

noncomputable section

namespace Work.MotT

open WeierstrassCurve WeierstrassCurve.Affine

variable {L Ω : Type*}

/-! ### Base change of the polynomial ring -/

/-- The `L`-algebra homomorphism `L[X] →ₐ[L] Ω[X]` given by applying `algebraMap L Ω` to the
coefficients, evaluated at `X` in the sense of `Polynomial.eval₂`. -/
private theorem eval₂_X_eq_map [CommSemiring L] [CommSemiring Ω] [Algebra L Ω] (p : Polynomial L) :
    Polynomial.eval₂ (algebraMap L (Polynomial Ω)) Polynomial.X p =
      Polynomial.map (algebraMap L Ω) p := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih => simp [ih]

/-- **Base change of the polynomial ring.**  `Ω ⊗[L] L[X] ≃ₐ[Ω] Ω[X]`, mapping `1 ⊗ₜ p` to the
polynomial obtained from `p` by applying `algebraMap L Ω` to its coefficients. -/
private noncomputable def tensorPolynomialAlgEquiv (L Ω : Type*) [CommSemiring L] [CommSemiring Ω]
    [Algebra L Ω] : TensorProduct L Ω (Polynomial L) ≃ₐ[Ω] Polynomial Ω :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom Ω Ω (Polynomial Ω))
      (Polynomial.aeval (Polynomial.X : Polynomial Ω)) (fun _ _ => Commute.all _ _))
    (Polynomial.aeval (TensorProduct.tmul L 1 Polynomial.X))
    (by
      apply Polynomial.algHom_ext
      simp [Algebra.TensorProduct.lift_tmul])
    (by
      apply Algebra.TensorProduct.ext
      · apply AlgHom.ext
        intro a
        simp [Algebra.TensorProduct.lift_tmul, Polynomial.aeval_X]
      · apply Polynomial.algHom_ext
        simp [Algebra.TensorProduct.lift_tmul, Polynomial.aeval_X])

@[simp]
private theorem tensorPolynomialAlgEquiv_tmul (L Ω : Type*) [CommSemiring L] [CommSemiring Ω]
    [Algebra L Ω] (p : Polynomial L) :
    tensorPolynomialAlgEquiv L Ω (TensorProduct.tmul L 1 p) =
      Polynomial.map (algebraMap L Ω) p := by
  show Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom Ω Ω (Polynomial Ω))
    (Polynomial.aeval (Polynomial.X : Polynomial Ω)) (fun _ _ => Commute.all _ _)
      (TensorProduct.tmul L 1 p) = Polynomial.map (algebraMap L Ω) p
  rw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, one_mul, Polynomial.aeval_def]
  exact eval₂_X_eq_map p

/-! ### Base change of the affine coordinate ring -/

/-- Base change of the Weierstrass polynomial. -/
private theorem polynomial_baseChange [CommRing L] [CommRing Ω] [Algebra L Ω] (W : WeierstrassCurve L) :
    (W.toAffine).polynomial.map (Polynomial.mapRingHom (algebraMap L Ω)) =
      (W.baseChange Ω).toAffine.polynomial := by
  ext n
  simp [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- **The base change of the affine coordinate ring of a Weierstrass curve is a domain.**
`Ω ⊗[L] L[W] ≅ Ω[W.baseChange Ω]`, the coordinate ring of the base-changed curve, which is an
integral domain. -/
private theorem isDomain_tensorCoordinateRing (L Ω : Type*) [Field L] [Field Ω] [Algebra L Ω]
    (W : WeierstrassCurve L) :
    IsDomain (TensorProduct L (WeierstrassCurve.Affine.CoordinateRing W) Ω) := by
  have he : ∀ p : Polynomial L,
      tensorPolynomialAlgEquiv L Ω (TensorProduct.tmul L 1 p) =
        Polynomial.map (algebraMap L Ω) p := tensorPolynomialAlgEquiv_tmul L Ω
  let inc : Polynomial L →+* TensorProduct L Ω (Polynomial L) :=
    (Algebra.TensorProduct.includeRight (R := L) (A := Ω) (B := Polynomial L)).toRingHom
  have hcomp : (tensorPolynomialAlgEquiv L Ω).toRingHom.comp inc =
      Polynomial.mapRingHom (algebraMap L Ω) := by
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom]
    change tensorPolynomialAlgEquiv L Ω (TensorProduct.tmul L 1 p) =
      Polynomial.map (algebraMap L Ω) p
    exact he p
  have hq : Polynomial.map (tensorPolynomialAlgEquiv L Ω).toRingHom
      (Polynomial.map inc (W.toAffine).polynomial) = (W.baseChange Ω).toAffine.polynomial := by
    rw [Polynomial.map_map, hcomp, polynomial_baseChange W]
  have hassoc : Associated (Polynomial.map (tensorPolynomialAlgEquiv L Ω).toRingHom
      (Polynomial.map inc (W.toAffine).polynomial)) ((W.baseChange Ω).toAffine.polynomial) := by
    rw [hq]
  let etensor := AdjoinRoot.tensorAlgEquiv (R := L) (S := Polynomial L) (T := Ω)
    (W.toAffine).polynomial (Polynomial.map inc (W.toAffine).polynomial) rfl
  let emap := AdjoinRoot.mapAlgEquiv (R := Ω) (tensorPolynomialAlgEquiv L Ω)
    (Polynomial.map inc (W.toAffine).polynomial) ((W.baseChange Ω).toAffine).polynomial hassoc
  have e1 : TensorProduct L Ω (WeierstrassCurve.Affine.CoordinateRing W) ≃ₐ[Ω]
      WeierstrassCurve.Affine.CoordinateRing (W.baseChange Ω) := etensor.trans emap
  exact MulEquiv.isDomain (WeierstrassCurve.Affine.CoordinateRing (W.baseChange Ω))
    ((Algebra.TensorProduct.comm L (WeierstrassCurve.Affine.CoordinateRing W) Ω).toMulEquiv.trans
      e1.toMulEquiv)

/-! ### The fraction ring of a domain whose base change is a domain -/

/-- **A fraction ring whose base change is a domain is a domain.**  If `F` is the fraction ring of
an integral domain `A` over a field `L`, and the base change `A ⊗[L] Ω` is a domain, then
`F ⊗[L] Ω` is a domain: it is the localisation of `Ω ⊗[L] A` at the image of the non-zero elements
of `A` (`IsLocalization.tensorProduct_tensorProduct_right`), and those elements are non-zero because
`A → Ω ⊗[L] A` is injective (`Module.Flat`, `Algebra.TensorProduct.includeRight_injective`). -/
theorem isDomain_tensor_of_isLocalization (L Ω A F : Type*) [Field L] [Field Ω] [Algebra L Ω]
    [CommRing A] [IsDomain A] [Algebra L A] [CommRing F] [Algebra L F] [Algebra A F]
    [IsScalarTower L A F] [IsLocalization (nonZeroDivisors A) F] [Module.Flat L A]
    [IsDomain (TensorProduct L A Ω)] :
    IsDomain (TensorProduct L F Ω) := by
  haveI : IsDomain (TensorProduct L Ω A) :=
    MulEquiv.isDomain (TensorProduct L A Ω) (Algebra.TensorProduct.comm L A Ω).symm.toMulEquiv
  letI instAlg : Algebra (TensorProduct L Ω A) (TensorProduct L Ω F) :=
    (Algebra.TensorProduct.map (AlgHom.id L Ω) (IsScalarTower.toAlgHom L A F)).toAlgebra
  haveI instST : IsScalarTower Ω (TensorProduct L Ω A) (TensorProduct L Ω F) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hloc : IsLocalization
      ((nonZeroDivisors A).map (Algebra.TensorProduct.includeRight (R := L) (A := Ω)))
      (TensorProduct L Ω F) :=
    IsLocalization.tensorProduct_tensorProduct_right L Ω (nonZeroDivisors A) F
      (by
        apply RingHom.ext
        intro a
        simp [RingHom.algebraMap_toAlgebra])
  have hN : (nonZeroDivisors A).map (Algebra.TensorProduct.includeRight (R := L) (A := Ω)) ≤
      nonZeroDivisors (TensorProduct L Ω A) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Submonoid.mem_map.mp hx
    have hminj : Function.Injective
        (Algebra.TensorProduct.includeRight (R := L) (A := Ω) (B := A)) :=
      Algebra.TensorProduct.includeRight_injective (R := L) (A := Ω) (B := A)
        (FaithfulSMul.algebraMap_injective L Ω)
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun h => nonZeroDivisors.ne_zero hm (hminj (by simpa using h))
  haveI hdom : IsDomain (TensorProduct L Ω F) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (TensorProduct L Ω F) hN
  exact MulEquiv.isDomain (TensorProduct L Ω F) (Algebra.TensorProduct.comm L F Ω).toMulEquiv

/-! ### The main theorem -/

/-- **Base change of the function field of a Weierstrass curve.**  For a Weierstrass curve
`W` over a field `L` with `W.Δ ≠ 0` and an algebraic field extension `Ω/L`, the base change
`L(W) ⊗_L Ω` of the function field of `W` is a field (equivalently, `L(W)` is linearly disjoint
from `Ω` over `L`; this is the regularity of the function field of a smooth curve).  Declare it in
namespace `Work.MotT`.

Route.  `CoordinateRing (W.baseChange Ω)` is a domain
(`WeierstrassCurve.Affine.CoordinateRing.instIsDomain`, from
`WeierstrassCurve.Affine.irreducible_polynomial`), and it is the base change of
`CoordinateRing W` along `L → Ω` (`WeierstrassCurve.Affine.CoordinateRing.map`, `map_mk`,
`map_injective`, `AdjoinRoot.tensorAlgEquiv`).  Hence `FunctionField W ⊗_L Ω =
Frac(CoordinateRing W) ⊗_L Ω` is the localisation of the domain `CoordinateRing (W.baseChange Ω)` at
the image of the nonzero elements of `CoordinateRing W`
(`IsLocalization.tensorProductEquivOfMapIncludeRight`), so a domain.  It is integral over the field
`FunctionField W = Frac(CoordinateRing W)` because `Ω/L` is algebraic, and a domain integral over a
subfield is a field (`isField_of_isIntegral_of_isField'`). -/
theorem isField_functionField_tensor (L Ω : Type*) [Field L] [Field Ω] [Algebra L Ω]
    [Algebra.IsAlgebraic L Ω] (W : WeierstrassCurve L) (hΔ : W.Δ ≠ 0) :
    IsField (TensorProduct L (WeierstrassCurve.Affine.FunctionField W) Ω) := by
  haveI hB : IsDomain (TensorProduct L (WeierstrassCurve.Affine.CoordinateRing W) Ω) :=
    isDomain_tensorCoordinateRing L Ω W
  haveI hdom : IsDomain (TensorProduct L (WeierstrassCurve.Affine.FunctionField W) Ω) :=
    isDomain_tensor_of_isLocalization L Ω (WeierstrassCurve.Affine.CoordinateRing W)
      (WeierstrassCurve.Affine.FunctionField W)
  exact Algebra.TensorProduct.isField_of_isAlgebraic L (WeierstrassCurve.Affine.FunctionField W) Ω
    (Or.inr ‹Algebra.IsAlgebraic L Ω›)

end Work.MotT
