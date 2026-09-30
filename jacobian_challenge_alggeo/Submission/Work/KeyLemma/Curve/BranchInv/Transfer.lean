/-
# Transferring the `K`-algebra structures on `N` along `k(h⁻¹) = k(h)`

For the second end of the pencil (the specialisation at `∞`, i.e. at a zero of `h⁻¹`) one wants to
run the branch argument *with the same Galois closure* `N` as for the first end, so that the two
generic values are literally the same element of `A(N)` (and hence the two end results are the two
sides of the statement).  Since `k(h⁻¹) = k(h)` (`Work.KeyLemma.Curve.baseField_inv`), the field
`N` (a finite Galois extension of `k(h)`) is also a finite Galois extension of `k(h⁻¹`) -- for the
`k(h⁻¹)`-algebra structure on `N` given by the composite `k(h⁻¹) → K(C) → N`.

The contents of this file are the bookkeeping for that: the inclusion `k(h) → k(h⁻¹)` given by the
identity on `K(C)`, and the transfer of `IsGalois`, `Algebra.IsSeparable`, `IsScalarTower` and
`FiniteDimensional` along it.
-/
import Mathlib
import Submission.Work.KeyLemma.Curve.ordBaseBaseField
import Submission.Work.KeyLemma.Curve.genericSum
import Submission.Work.CurveBasics.Order.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry Limits
open scoped Classical

universe u

namespace Work.KeyLemma.Curve

open Work.CurveBasics

variable {k : Type u} [Field k]

/-- The inclusion `k(h) ⊆ k(h⁻¹)`, i.e. the identity on `K(C)`. -/
noncomputable def baseFieldIncl (C : Curve k) {h : C.functionField} (hh : h ≠ 0) :
    ↥(baseField C h) →ₐ[k] ↥(baseField C h⁻¹) :=
  IntermediateField.inclusion (le_of_eq (baseField_inv C hh).symm)

/-- The inclusion `k(h) ⊆ k(h⁻¹)` is the identity on `K(C)`. -/
theorem baseFieldIncl_coe (C : Curve k) {h : C.functionField} (hh : h ≠ 0)
    (x : ↥(baseField C h)) :
    ((baseFieldIncl C hh x : ↥(baseField C h⁻¹)) : C.functionField) = (x : C.functionField) :=
  IntermediateField.coe_inclusion _ x

/-- The same, read through the structure map of `K(C)`. -/
theorem baseFieldIncl_algebraMap (C : Curve k) {h : C.functionField} (hh : h ≠ 0)
    (x : ↥(baseField C h)) :
    algebraMap ↥(baseField C h⁻¹) ↥C.functionField (baseFieldIncl C hh x)
      = algebraMap ↥(baseField C h) ↥C.functionField x := by
  rw [IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply]
  exact baseFieldIncl_coe C hh x

/-- The compatibility of the composite `k(h⁻¹)`-algebra structure on `N` with the `k(h)`-one,
when both are composites through `K(C)`. -/
theorem algebraMap_baseFieldIncl {C : Curve k} {h : C.functionField} (hh : h ≠ 0)
    {N : Type u} [Field N]
    [Algebra ↥(baseField C h) N] [Algebra ↥(baseField C h⁻¹) N] [Algebra ↥C.functionField N]
    (hKE : (algebraMap ↥(baseField C h) N)
      = (algebraMap ↥C.functionField N).comp (algebraMap ↥(baseField C h) ↥C.functionField))
    (hKE' : (algebraMap ↥(baseField C h⁻¹) N)
      = (algebraMap ↥C.functionField N).comp (algebraMap ↥(baseField C h⁻¹) ↥C.functionField))
    (x : ↥(baseField C h)) :
    algebraMap ↥(baseField C h⁻¹) N (baseFieldIncl C hh x) = algebraMap ↥(baseField C h) N x := by
  rw [hKE', hKE, RingHom.comp_apply, RingHom.comp_apply, baseFieldIncl_algebraMap C hh x]

section NInstances

variable {C : Curve k} {h : C.functionField} (hh : h ≠ 0)
variable {N : Type u} [Field N] [Algebra ↥(baseField C h) N] [Algebra ↥(baseField C h⁻¹) N]

/-- **`N` is Galois over `k(h⁻¹)`** for the composite `k(h⁻¹)`-algebra structure on `N`, provided
the compatibility with the `k(h)`-structure holds. -/
theorem isGalois_baseField_inv [IsGalois ↥(baseField C h) N]
    (hcomp : ∀ x : ↥(baseField C h),
      algebraMap ↥(baseField C h⁻¹) N (baseFieldIncl C hh x) = algebraMap ↥(baseField C h) N x) :
    IsGalois ↥(baseField C h⁻¹) N := by
  letI : Algebra ↥(baseField C h) ↥(baseField C h⁻¹) :=
    (baseFieldIncl C hh).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(baseField C h) ↥(baseField C h⁻¹) N :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (hcomp x).symm
  exact IsGalois.tower_top_of_isGalois ↥(baseField C h) ↥(baseField C h⁻¹) N

/-- **Finiteness transfers**: `N` is finite over `k(h⁻¹)` as soon as it is finite over `k(h)` and
the two algebra structures are compatible. -/
theorem finiteDimensional_baseField_inv [FiniteDimensional ↥(baseField C h) N]
    (hcomp : ∀ x : ↥(baseField C h),
      algebraMap ↥(baseField C h⁻¹) N (baseFieldIncl C hh x) = algebraMap ↥(baseField C h) N x) :
    FiniteDimensional ↥(baseField C h⁻¹) N := by
  letI : Algebra ↥(baseField C h) ↥(baseField C h⁻¹) :=
    (baseFieldIncl C hh).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(baseField C h) ↥(baseField C h⁻¹) N :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (hcomp x).symm
  exact Module.Finite.of_restrictScalars_finite ↥(baseField C h) ↥(baseField C h⁻¹) N

end NInstances

/-- **`K(C)/k(h⁻¹)` is separable** for the ambient subfield inclusions, as soon as
`K(C)/k(h)` is. -/
theorem isSeparable_baseField_inv {C : Curve k} {h : C.functionField} (hh : h ≠ 0)
    [Algebra.IsSeparable ↥(baseField C h) ↥C.functionField] :
    Algebra.IsSeparable ↥(baseField C h⁻¹) ↥C.functionField := by
  letI : Algebra ↥(baseField C h) ↥(baseField C h⁻¹) :=
    (baseFieldIncl C hh).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(baseField C h) ↥(baseField C h⁻¹) ↥C.functionField :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, IntermediateField.algebraMap_apply,
        IntermediateField.algebraMap_apply]
      exact (baseFieldIncl_coe C hh x).symm
  exact Algebra.isSeparable_tower_top_of_isSeparable ↥(baseField C h) ↥(baseField C h⁻¹)
    ↥C.functionField


/-- **The ambient tower `k(h⁻¹) ⊆ K(C) ⊆ N`.** -/
theorem isScalarTower_baseField_functionField {C : Curve k} {h : C.functionField} (hh : h ≠ 0)
    {N : Type u} [Field N] [Algebra ↥C.functionField N] :
    IsScalarTower ↥(baseField C h⁻¹) ↥C.functionField N := by
  refine ⟨fun a b c => ?_⟩
  have hab : (a • b : C.functionField) = (a : C.functionField) * b := rfl
  have h2 : ∀ (u : ↥(baseField C h⁻¹)) (c : N), (u • c : N) = (u : C.functionField) • c :=
    fun u c => rfl
  have h3 : ∀ (u : C.functionField) (c : N),
      (u • c : N) = algebraMap ↥C.functionField N u * c := fun u c => Algebra.smul_def u c
  simp only [hab, h2, h3, Algebra.smul_def, map_mul, mul_assoc]

/-- **The ambient tower `k[h⁻¹] ⊆ k(h⁻¹) ⊆ N`.** -/
theorem isScalarTower_ordBase_baseField {C : Curve k} {h : C.functionField} (hh : h ≠ 0)
    {N : Type u} [Field N] [Algebra ↥C.functionField N] [Algebra ↥(baseField C h⁻¹) N]
    [Algebra ↥(C.ordBase h⁻¹) N]
    (hAK : ∀ x : ↥(C.ordBase h⁻¹),
      (algebraMap ↥(C.ordBase h⁻¹) ↥(baseField C h⁻¹) x : C.functionField)
        = (x : C.functionField)) :
    IsScalarTower ↥(C.ordBase h⁻¹) ↥(baseField C h⁻¹) N := by
  refine ⟨fun a b c => ?_⟩
  have h1 : (a • b : ↥(baseField C h⁻¹))
      = algebraMap ↥(C.ordBase h⁻¹) ↥(baseField C h⁻¹) a * b := Algebra.smul_def a b
  have h2 : ∀ (u : ↥(baseField C h⁻¹)) (c : N), (u • c : N) = (u : C.functionField) • c :=
    fun u c => rfl
  have h3 : ∀ (u : ↥(C.ordBase h⁻¹)) (c : N), (u • c : N) = (u : C.functionField) • c :=
    fun u c => rfl
  have h4 : ∀ (t : C.functionField) (c : N),
      (t • c : N) = algebraMap ↥C.functionField N t * c := fun t c => Algebra.smul_def t c
  have hAB : ((algebraMap ↥(C.ordBase h⁻¹) ↥(baseField C h⁻¹) a * b : ↥(baseField C h⁻¹))
        : C.functionField) = (a : C.functionField) * (b : C.functionField) := by
    rw [IntermediateField.coe_mul, hAK a]
  simp only [h1, h2, h3, h4, hAB, Algebra.smul_def, map_mul, mul_assoc]


/-- **`k[u]^{int}_N` is Dedekind.**  Stated in a context where the algebra structures on `N` are
the canonical ones, so that it can be applied to the *composite* structures used for the second
end of the pencil. -/
theorem isDedekindDomain_integralClosure {C : Curve k} (u : C.functionField)
    {N : Type u} [Field N] [Algebra ↥(C.ordBase u) N] [Algebra ↥(baseField C u) N]
    [IsFractionRing ↥(C.ordBase u) ↥(baseField C u)]
    [IsScalarTower ↥(C.ordBase u) ↥(baseField C u) N]
    [FiniteDimensional ↥(baseField C u) N]
    [Algebra.IsSeparable ↥(baseField C u) N] :
    IsDedekindDomain ↥(integralClosure ↥(C.ordBase u) N) :=
  integralClosure.isDedekindDomain ↥(C.ordBase u) ↥(baseField C u) N

/-- **`N` is the fraction ring of `k[u]^{int}_N`**, again in the canonical context. -/
theorem isFractionRing_integralClosure {C : Curve k} (u : C.functionField)
    {N : Type u} [Field N] [Algebra ↥(C.ordBase u) N] [Algebra ↥(baseField C u) N]
    [IsFractionRing ↥(C.ordBase u) ↥(baseField C u)]
    [IsScalarTower ↥(C.ordBase u) ↥(baseField C u) N]
    [FiniteDimensional ↥(baseField C u) N]
    [Algebra.IsSeparable ↥(baseField C u) N] :
    IsFractionRing ↥(integralClosure ↥(C.ordBase u) N) N :=
  integralClosure.isFractionRing_of_finite_extension (A := ↥(C.ordBase u))
    ↥(baseField C u) N

/-- The composite `k(h⁻¹)`-algebra structure on `N` is `k`-linear, as soon as the `k`-action on
`N` is the one induced by the `k`-action on `K(C)`. -/
theorem isScalarTower_k_baseField_inv {C : Curve k} {h : C.functionField} (hh : h ≠ 0)
    {N : Type u} [Field N] [Algebra k N] [Algebra ↥(baseField C h⁻¹) N]
    [Algebra ↥C.functionField N]
    (hkE : ∀ x : k,
      algebraMap k N x = algebraMap ↥C.functionField N (algebraMap k ↥C.functionField x)) :
    IsScalarTower k ↥(baseField C h⁻¹) N := by
  refine ⟨fun a b c => ?_⟩
  have hb : (a • b : ↥(baseField C h⁻¹)) = algebraMap k ↥(baseField C h⁻¹) a * b :=
    Algebra.smul_def a b
  have hcoe : ((algebraMap k ↥(baseField C h⁻¹) a * b : ↥(baseField C h⁻¹)) : C.functionField)
      = algebraMap k ↥C.functionField a * (b : C.functionField) := by
    rw [IntermediateField.coe_mul, IntermediateField.coe_algebraMap_apply]
  have hsmul : ∀ (u : ↥(baseField C h⁻¹)) (c : N), (u • c : N) = (u : C.functionField) • c :=
    fun u c => rfl
  have hsmulE : ∀ (t : C.functionField) (c : N),
      (t • c : N) = algebraMap ↥C.functionField N t * c := fun t c => Algebra.smul_def t c
  conv_lhs => rw [hb]
  rw [hsmul, hcoe, hsmulE, hsmul, hsmulE, map_mul, Algebra.smul_def, hkE a, mul_assoc]

end Work.KeyLemma.Curve
