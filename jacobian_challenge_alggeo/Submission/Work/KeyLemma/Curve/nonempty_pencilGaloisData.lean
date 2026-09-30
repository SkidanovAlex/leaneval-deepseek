import Mathlib
import Submission.Work.KeyLemma.Curve.pencilGaloisData
import Submission.Work.KeyLemma.Curve.ordBaseBaseField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
open CategoryTheory AlgebraicGeometry Limits
open scoped Classical

universe u

namespace Work.KeyLemma.Curve

open Work.CurveBasics

/-- **A Galois closure for the pencil of `h`.**

Let `k` be a field, `C` a curve over `k`, `h ∈ K(C)` transcendental over `k`, and suppose that
`K := k(h) ⊆ E := K(C)` is finite and separable.  Then there is a field `N` which is a finite
Galois extension of `K` containing `E` over `K` together with the `k`- and `k[h]`-algebra
structures, i.e. `PencilGaloisData k C h`.

Construction: let `α : E` be a primitive element of `E/K`, `f := minpoly K α` and
`N := Polynomial.SplittingField f`. -/
theorem nonempty_pencilGaloisData {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (h : C.functionField) (hht : Transcendental k h)
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    [Algebra.IsSeparable ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField] :
    Nonempty (Work.KeyLemma.Curve.PencilGaloisData k C h) := by
  obtain ⟨α, hα⟩ :=
    Field.exists_primitive_element ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField
  have hint : IsIntegral ↥(Work.KeyLemma.Curve.baseField C h) α :=
    Algebra.IsSeparable.isIntegral _ α
  let f : Polynomial ↥(Work.KeyLemma.Curve.baseField C h) :=
    minpoly ↥(Work.KeyLemma.Curve.baseField C h) α
  let N := Polynomial.SplittingField f
  letI hNKSF : Algebra ↥(Work.KeyLemma.Curve.baseField C h) N :=
    Polynomial.SplittingField.instAlgebra_1 f
  haveI hsplitSF : Polynomial.IsSplittingField ↥(Work.KeyLemma.Curve.baseField C h) N f :=
    Polynomial.IsSplittingField.splittingField f
  have hfinSF : FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) N := inferInstance
  have hsep : f.Separable := Algebra.IsSeparable.isSeparable _ α
  have hgalSF : IsGalois ↥(Work.KeyLemma.Curve.baseField C h) N :=
    IsGalois.of_separable_splitting_field (p := f) hsep
  have hdeg :
      (Polynomial.map (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N) f).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective
      (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N).injective f]
    exact ne_of_gt (minpoly.degree_pos hint)
  obtain ⟨β, hβ⟩ := (Polynomial.SplittingField.splits f).exists_eval_eq_zero hdeg
  have hβ' : Polynomial.eval₂ (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N) β f = 0 := by
    rw [← Polynomial.eval_map]
    exact hβ
  let e1 := IntermediateField.adjoinRootEquivAdjoin ↥(Work.KeyLemma.Curve.baseField C h) hint
  let e2 := (IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv
  let e := e2.symm.trans e1.symm
  let ψ : AdjoinRoot f →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId _ N) β (by simpa using hβ')
  let φ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N := ψ.comp e.toAlgHom
  letI hNE : Algebra ↥C.functionField N := (φ.toRingHom).toAlgebra
  have hKEsf : @algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N _ _ hNKSF
      = (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField) := by
    rw [show (algebraMap ↥C.functionField N) = φ.toRingHom from
      RingHom.algebraMap_toAlgebra φ.toRingHom]
    ext x
    exact (φ.commutes x).symm
  have hAlgDerived :
      hNKSF = (Work.KeyLemma.Curve.baseField C h).instAlgebraSubtypeMem := by
    apply Algebra.algebra_ext
    intro x
    rw [RingHom.ext_iff.mp hKEsf x]
    rfl
  rw [hAlgDerived] at hfinSF hgalSF hsplitSF
  letI algK : Algebra ↥(Work.KeyLemma.Curve.baseField C h) N :=
    (Work.KeyLemma.Curve.baseField C h).instAlgebraSubtypeMem
  letI algk : Algebra k N := Polynomial.SplittingField.instAlgebra f
  letI algA : Algebra ↥(C.ordBase h) N := inferInstance
  have hAlgKMap : (@algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N _ _ hNKSF) =
      (@algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N _ _
        (Work.KeyLemma.Curve.baseField C h).instAlgebraSubtypeMem) := by
    rw [hKEsf]
    rfl
  have hA : (algebraMap k N) =
      (@algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N _ _ hNKSF).comp
        (algebraMap k ↥(Work.KeyLemma.Curve.baseField C h)) := rfl
  haveI hTK : IsScalarTower k ↥(Work.KeyLemma.Curve.baseField C h) N :=
    IsScalarTower.of_algebraMap_eq (R := k)
      (S := ↥(Work.KeyLemma.Curve.baseField C h)) (A := N) (fun x => by
      rw [hA]
      simp only [RingHom.comp_apply]
      rw [RingHom.ext_iff.mp hKEsf (algebraMap k ↥(Work.KeyLemma.Curve.baseField C h) x)]
      rfl)
  haveI hTE : IsScalarTower ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField N :=
    inferInstance
  haveI hTAK : IsScalarTower ↥(C.ordBase h) ↥(Work.KeyLemma.Curve.baseField C h) N :=
    IsScalarTower.of_algebraMap_eq (R := ↥(C.ordBase h))
      (S := ↥(Work.KeyLemma.Curve.baseField C h)) (A := N) (fun x => rfl)
  haveI hTAE : IsScalarTower ↥(C.ordBase h) ↥C.functionField N := inferInstance
  haveI hfin : FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) N := hfinSF
  haveI hgal : IsGalois ↥(Work.KeyLemma.Curve.baseField C h) N := hgalSF
  haveI hfrac : IsFractionRing ↥(integralClosure ↥(C.ordBase h) N) N :=
    integralClosure.isFractionRing_of_finite_extension ↥(Work.KeyLemma.Curve.baseField C h) N
  have hKE : (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N) =
      (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField) := rfl
  have hAE : (algebraMap ↥(C.ordBase h) N) =
      (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(C.ordBase h) ↥C.functionField) := rfl
  exact ⟨N, hKE, hAE⟩

end Work.KeyLemma.Curve
