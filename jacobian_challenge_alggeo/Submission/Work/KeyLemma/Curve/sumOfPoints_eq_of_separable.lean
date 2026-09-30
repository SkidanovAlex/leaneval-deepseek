import Mathlib
import Submission.Work.KeyLemma.Curve.nonempty_pencilGaloisData
import Submission.Work.KeyLemma.Curve.pencilGaloisData
import Submission.Work.KeyLemma.Curve.pencilAssembly
import Submission.Work.KeyLemma.Curve.p1FunctionField_iso
import Submission.Work.KeyLemma.Curve.ordBaseBaseField
import Submission.Work.KeyLemma.Curve.branch_sum
import Submission.Work.KeyLemma.Curve.BranchInv.Transfer
import Submission.Work.KeyLemma.Curve.BranchInv.SecondEnd
import Submission.Work.KeyLemma.Curve.BranchInv.BranchEnd
import Submission.Work.KeyLemma.Curve.pencil_of_separable
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField
import Submission.Work.CurveBasics.Basic
import Submission.Work.SpecLin.Setup.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

set_option maxHeartbeats 2000000

namespace Work.KeyLemma.Curve

universe u

variable {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
variable {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
variable [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A] [AlgebraicGeometry.IsProper A.hom]
variable (f : C.toOver ⟶ A) (h : C.functionField)

/-- The separable case of the pencil statement: for `k` algebraically closed, `C` a curve, `A` a
proper commutative group scheme over `k`, `f : C.toOver ⟶ A`, and `h ≠ 0` nonconstant with
`K(C)/k(h)` separable, the sums of the images of the models of `div₀ h` and `div_∞ h` agree.
This is exactly the hypothesis `H` of `Work.KeyLemma.Curve.pencil_general_of_separable`, which
turns it into the pencil statement for all `h`.  The full recipe (reduction to the generic-fibre
sum `genericSum`, the branch specialisation `exists_branch_sum_fixed`, the descent
`exists_const_eq_genericSum`, and the second end via `genericSum_inv`) is in
`Submission/Work/KeyLemma/Curve/NOTES_pencil.md` sect. 14.2 and 15, and a complete draft proof is
kept at `Submission/Work/KeyLemma/Curve/_mine/wiring_skeleton.txt`; sect. 15.2 explains the
typeclass-instance trap (`IsScalarTower ↥S ↥T N` for subobjects of `K(C)`) which is the only
obstacle there. -/
theorem sumOfPoints_eq_of_separable {k : Type u} [Field k] [IsAlgClosed k]
    {C : Work.CurveBasics.Curve k}
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A] [AlgebraicGeometry.IsProper A.hom]
    (f : C.toOver ⟶ A) :
    ∀ (h : C.functionField), h ≠ 0 → ¬ Work.KeyLemma.Curve.IsConstant C h →
      Algebra.IsSeparable ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField →
      ∀ s₀ s₁ : Work.KeyLemma.Curve.SumDiv C,
        Work.KeyLemma.Curve.SumDiv.toDiv C s₀ = Work.KeyLemma.Curve.posPart C h →
        Work.KeyLemma.Curve.SumDiv.toDiv C s₁ = Work.KeyLemma.Curve.negPart C h →
        Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s₀
          = Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s₁ := by
  intro h hh hnc hsep s₀ s₁ hs₀ hs₁
  classical
  have hht : Transcendental k h := fun halg =>
    hnc (Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic C halg)
  haveI hfin : FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField :=
    Work.CurveBasics.Order.finiteDimensional_adjoin_functionField C hht
  -- the Galois closure of `K(C)/k(h)`
  obtain ⟨D⟩ := Work.KeyLemma.Curve.nonempty_pencilGaloisData (k := k) C h hht
  letI hNf : Field D.N := D.fieldN
  letI hNk : Algebra k D.N := D.algk
  letI hNE : Algebra ↥C.functionField D.N := D.algE
  letI hNK : Algebra ↥(Work.KeyLemma.Curve.baseField C h) D.N :=
    IntermediateField.instAlgebraSubtypeMem (Work.KeyLemma.Curve.baseField C h)
  letI hNA : Algebra ↥(C.ordBase h) D.N := D.algA
  have hAE : (algebraMap ↥(C.ordBase h) D.N)
      = (algebraMap ↥C.functionField D.N).comp
        (algebraMap ↥(C.ordBase h) ↥C.functionField) := D.hAE
  have hKE : (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) D.N)
      = (algebraMap ↥C.functionField D.N).comp
        (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField) := rfl
  letI hTAK1 : IsScalarTower ↥(C.ordBase h) ↥(Work.KeyLemma.Curve.baseField C h) D.N :=
    D.stAK
  letI hTAE1 : IsScalarTower ↥(C.ordBase h) ↥C.functionField D.N := D.stAE
  letI hSMA : SMul ↥(C.ordBase h) D.N := hNA.toSMul
  letI hSMo : SMul ↥(C.ordBase h) ↥(Work.KeyLemma.Curve.baseField C h) :=
    (Work.KeyLemma.Curve.instAlgebraOrdBaseBaseField k C h).toSMul
  letI hTK : IsScalarTower k ↥(Work.KeyLemma.Curve.baseField C h) D.N := D.stkK
  letI hTE : IsScalarTower ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField D.N := D.stKE
  letI hTAK : IsScalarTower ↥(C.ordBase h) ↥(Work.KeyLemma.Curve.baseField C h) D.N :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      calc (algebraMap ↥(C.ordBase h) D.N) x
          = (algebraMap ↥C.functionField D.N)
              ((algebraMap ↥(C.ordBase h) ↥C.functionField) x) :=
            congrFun (congrArg DFunLike.coe hAE) x
        _ = (algebraMap ↥C.functionField D.N)
              ((algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField)
                (algebraMap ↥(C.ordBase h) ↥(Work.KeyLemma.Curve.baseField C h) x)) := by
            congr 1
        _ = (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) D.N)
              (algebraMap ↥(C.ordBase h) ↥(Work.KeyLemma.Curve.baseField C h) x) :=
            (congrFun (congrArg DFunLike.coe hKE) _).symm)
  letI hTAE : IsScalarTower ↥(C.ordBase h) ↥C.functionField D.N :=
    IsScalarTower.of_algebraMap_eq (fun x => congrFun (congrArg DFunLike.coe hAE) x)
  letI hNfin : FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) D.N := D.fin
  haveI hNg : IsGalois ↥(Work.KeyLemma.Curve.baseField C h) D.N :=
    @IsGalois.of_equiv_equiv ↥(Work.KeyLemma.Curve.baseField C h) D.N
      (Work.KeyLemma.Curve.baseField C h).toField D.fieldN D.algK
      ↥(Work.KeyLemma.Curve.baseField C h) D.N D.fieldN (Work.KeyLemma.Curve.baseField C h).toField
      (IntermediateField.instAlgebraSubtypeMem (Work.KeyLemma.Curve.baseField C h)) D.galois
      (RingEquiv.refl ↥(Work.KeyLemma.Curve.baseField C h)) (RingEquiv.refl D.N) (by
        show ((algebraMap ↥(Work.KeyLemma.Curve.baseField C h) D.N :
            ↥(Work.KeyLemma.Curve.baseField C h) →+* D.N).comp
          (RingHom.id ↥(Work.KeyLemma.Curve.baseField C h))) = (RingHom.id D.N).comp (D.algK.algebraMap)
        rw [RingHom.comp_id, RingHom.id_comp]
        exact D.hKE.symm)
  letI hNfr : IsFractionRing ↥(integralClosure ↥(C.ordBase h) D.N) D.N := D.frac
  -- the `k`-point whose base change to `N` is the generic-fibre sum
  obtain ⟨dP1⟩ := Work.KeyLemma.Curve.p1FunctionField_iso (k := k) C hht
  obtain ⟨c, hc⟩ := Work.KeyLemma.Curve.exists_const_eq_genericSum (C := C) (h := h) (N := D.N) f dP1
  -- the `k`-action on `N` is the one induced by the `k`-action on `K(C)`
  have hkE : ∀ x : k, algebraMap k D.N x
      = algebraMap ↥C.functionField D.N (algebraMap k ↥C.functionField x) := by
    intro x
    rw [IsScalarTower.algebraMap_apply k ↥(Work.KeyLemma.Curve.baseField C h) D.N x, hKE,
      RingHom.comp_apply]
    exact congrArg (algebraMap ↥C.functionField D.N)
      (IsScalarTower.algebraMap_apply k ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField x)
  -- ## the first end: the coordinate `h`
  have h0 : Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s₀ = c :=
    branch_end (C := C) (A := A) h hht h hht hh f (N := D.N) hKE hAE hkE rfl c hc D.frac
      (isDedekindDomain_integralClosure (C := C) h) s₀ hs₀
  -- ## the second end: the coordinate `h⁻¹`, with the same `N`
  have h1 : Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s₁ = c := by
    -- the `k(h⁻¹)`- and `k[h⁻¹]`-algebra structures on `N`
    letI : Algebra ↥(Work.KeyLemma.Curve.baseField C h⁻¹) D.N :=
      (Work.KeyLemma.Curve.baseField C h⁻¹).instAlgebraSubtypeMem
    letI : Algebra ↥(C.ordBase h⁻¹) D.N := inferInstance
    have hKE' : (algebraMap ↥(Work.KeyLemma.Curve.baseField C h⁻¹) D.N)
        = (algebraMap ↥C.functionField D.N).comp
          (algebraMap ↥(Work.KeyLemma.Curve.baseField C h⁻¹) ↥C.functionField) := rfl
    have hAE' : (algebraMap ↥(C.ordBase h⁻¹) D.N)
        = (algebraMap ↥C.functionField D.N).comp
          (algebraMap ↥(C.ordBase h⁻¹) ↥C.functionField) := rfl
    have hcomp : ∀ (x : ↥(Work.KeyLemma.Curve.baseField C h))
        (y : ↥(Work.KeyLemma.Curve.baseField C h⁻¹)),
        (x : C.functionField) = (y : C.functionField) →
          algebraMap ↥(Work.KeyLemma.Curve.baseField C h) D.N x
            = algebraMap ↥(Work.KeyLemma.Curve.baseField C h⁻¹) D.N y := by
      intro x y hxy
      rw [hKE, hKE']
      exact congrArg (algebraMap ↥C.functionField D.N) hxy
    have hcompIncl : ∀ x : ↥(Work.KeyLemma.Curve.baseField C h),
        algebraMap ↥(Work.KeyLemma.Curve.baseField C h⁻¹) D.N
            (baseFieldIncl C hh x) = algebraMap ↥(Work.KeyLemma.Curve.baseField C h) D.N x :=
      fun x => algebraMap_baseFieldIncl (C := C) hh hKE hKE' x
    haveI hgal' : IsGalois ↥(Work.KeyLemma.Curve.baseField C h⁻¹) D.N :=
      isGalois_baseField_inv (N := D.N) hh hcompIncl
    haveI hfin' : FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h⁻¹) D.N :=
      finiteDimensional_baseField_inv (N := D.N) hh hcompIncl
    haveI hSTk' : IsScalarTower k ↥(Work.KeyLemma.Curve.baseField C h⁻¹) D.N :=
      isScalarTower_k_baseField_inv (C := C) (h := h) hh hkE
    haveI hSTKE' : IsScalarTower ↥(Work.KeyLemma.Curve.baseField C h⁻¹) ↥C.functionField D.N :=
      isScalarTower_baseField_functionField (C := C) (h := h) hh
    haveI hSTAK' : IsScalarTower ↥(C.ordBase h⁻¹)
        ↥(Work.KeyLemma.Curve.baseField C h⁻¹) D.N :=
      isScalarTower_ordBase_baseField (C := C) (h := h) hh
        (fun x => algebraMap_ordBase_baseField k C h⁻¹ x)
    haveI hfinE' : FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h⁻¹) ↥C.functionField :=
      Work.CurveBasics.Order.finiteDimensional_adjoin_functionField C
        (transcendental_inv (C := C) (h := h) hht)
    haveI hsepE' : Algebra.IsSeparable ↥(Work.KeyLemma.Curve.baseField C h⁻¹) ↥C.functionField :=
      isSeparable_baseField_inv (C := C) (h := h) hh
    have hg : genericSum (C := C) (h := h⁻¹) (N := D.N) f
        = genericSum (C := C) (h := h) (N := D.N) f :=
      genericSum_inv_comp (C := C) (h := h) hh hcomp (f := f)
    have hded : IsDedekindDomain ↥(integralClosure ↥(C.ordBase h⁻¹) D.N) :=
      isDedekindDomain_integralClosure (C := C) h⁻¹
    have hfrac : IsFractionRing ↥(integralClosure ↥(C.ordBase h⁻¹) D.N) D.N :=
      isFractionRing_integralClosure (C := C) h⁻¹
    exact branch_end (C := C) (A := A) h hht h⁻¹
      (transcendental_inv (C := C) (h := h) hht) (inv_ne_zero hh) f (N := D.N)
      hKE' hAE' hkE hg c hc hfrac hded s₁
      (by rw [← Work.KeyLemma.Curve.negPart_eq_posPart_inv C hh]; exact hs₁)
  rw [h0, h1]

end Work.KeyLemma.Curve
