/-
# One end of the pencil: from the branch sum to `Σ f(s) = c`

The branch sum `Work.KeyLemma.Curve.branch_sum` computes, for a prime `P` over `(u)` in the
integral closure `k[u]^{int}_N`, a morphism `ρ : Spec R' ⟶ A` (`R' = (k[u]^{int}_N)_P`) whose
generic value is the generic-fibre sum and whose closed value is `Σ f(s)` for a model `s` of
`posPart C u`.  Combined with a `k`-point `c` of `A` whose base change to `N` is the generic-fibre
sum (`Work.KeyLemma.Curve.exists_const_eq_genericSum`) and the separatedness of `A`
(`Work.KeyLemma.Curve.sumOfPoints_eq_of_branch`), this gives `Σ f(s) = c`.

Here the coordinate `u` is arbitrary (it is `h` for the first end and `h⁻¹` for the second), while
the subfield `k(u) ⊆ N` is the one of the branch statement; for the second end it is the composite
`k(h⁻¹) → K(C) → N`.
-/
import Mathlib
import Submission.Work.KeyLemma.Curve.branch_sum
import Submission.Work.KeyLemma.Curve.pencilAssembly
import Submission.Work.KeyLemma.Curve.BranchInv.SecondEnd
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2000000
open CategoryTheory AlgebraicGeometry Limits
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.KeyLemma.Curve

open Work.CurveBasics Work.SpecLin

/-- **One end of the pencil.** -/
theorem branch_end {k : Type u} [Field k] [IsAlgClosed k]
    {C : Curve k} (h : C.functionField) (hht : Transcendental k h)
    (u : C.functionField) (hut : Transcendental k u) (hu0 : u ≠ 0)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    (f : C.toOver ⟶ A)
    [FiniteDimensional ↥(baseField C h) ↥C.functionField]
    [Algebra.IsSeparable ↥(baseField C h) ↥C.functionField]
    {N : Type u} [Field N] [Algebra k N]
    [Algebra ↥(baseField C h) N] [IsScalarTower k ↥(baseField C h) N]
    [Algebra ↥(baseField C u) N] [IsScalarTower k ↥(baseField C u) N]
    [IsGalois ↥(baseField C u) N]
    [Algebra ↥C.functionField N] [IsScalarTower ↥(baseField C u) ↥C.functionField N]
    [FiniteDimensional ↥(baseField C u) N]
    [FiniteDimensional ↥(baseField C u) ↥C.functionField]
    [Algebra.IsSeparable ↥(baseField C u) ↥C.functionField]
    [Algebra ↥(C.ordBase u) N]
    [IsScalarTower ↥(C.ordBase u) ↥(baseField C u) N]
    (hKE : (algebraMap ↥(baseField C u) N)
      = (algebraMap ↥C.functionField N).comp (algebraMap ↥(baseField C u) ↥C.functionField))
    (hAE : (algebraMap ↥(C.ordBase u) N)
      = (algebraMap ↥C.functionField N).comp (algebraMap ↥(C.ordBase u) ↥C.functionField))
    (hkE : ∀ x : k,
      algebraMap k N x = algebraMap ↥C.functionField N (algebraMap k ↥C.functionField x))
    (hg : genericSum (C := C) (h := u) (N := N) f = genericSum (C := C) (h := h) (N := N) f)
    (c : Pt k A)
    (hc : Spec.map (CommRingCat.ofHom (algebraMap k N)) ≫ c.leftHom
      = genericSum (C := C) (h := h) (N := N) f)
    (hC'frac : IsFractionRing ↥(integralClosure ↥(C.ordBase u) N) N)
    (hDed : IsDedekindDomain ↥(integralClosure ↥(C.ordBase u) N))
    (s : SumDiv C) (hs : SumDiv.toDiv C s = posPart C u) :
    SumDiv.sumOfPoints C f s = c := by
  classical
  -- ## the prime `P` over `(u)`
  haveI hpri : (C.ordIdeal u).IsPrime := Work.CurveBasics.Order.ordIdeal_isPrime C u hut
  have hunderbot : Ideal.under ↥(C.ordBase u)
      (⊥ : Ideal ↥(integralClosure ↥(C.ordBase u) N)) = (⊥ : Ideal ↥(C.ordBase u)) := by
    rw [Ideal.under]
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx1 : (algebraMap ↥(C.ordBase u) ↥(integralClosure ↥(C.ordBase u) N)) x = 0 :=
      Ideal.mem_bot.mp (Ideal.mem_comap.mp hx)
    have hx2 : (algebraMap ↥(C.ordBase u) N) x = 0 := by
      rw [IsScalarTower.algebraMap_apply ↥(C.ordBase u)
        ↥(integralClosure ↥(C.ordBase u) N) N, hx1, map_zero]
    have hx3 : (algebraMap ↥C.functionField N) ((algebraMap ↥(C.ordBase u) ↥C.functionField) x) = 0 := by
      rw [← RingHom.comp_apply, ← hAE, hx2]
    refine Ideal.mem_bot.mpr (Subtype.ext ?_)
    show ((x : ↥(C.ordBase u)) : C.functionField) = 0
    exact FaithfulSMul.algebraMap_injective ↥C.functionField N (by simpa using hx3)
  obtain ⟨P, -, hPprime, hPunder⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (R := ↥(C.ordBase u)) (S := ↥(integralClosure ↥(C.ordBase u) N)) (C.ordIdeal u)
    (⊥ : Ideal ↥(integralClosure ↥(C.ordBase u) N)) (by rw [hunderbot]; exact bot_le)
  letI hPprimeI : P.IsPrime := hPprime
  haveI hPover : P.LiesOver (C.ordIdeal u) := ⟨hPunder.symm⟩
  -- ## the `k[u] → k(u)`-linearity of `σ`-compatibilities, in equational form
  have hcanon : ∀ x : ↥(C.ordBase u),
      algebraMap ↥(baseField C u) N (algebraMap ↥(C.ordBase u) ↥(baseField C u) x)
        = algebraMap ↥(C.ordBase u) N x := by
    intro x
    rw [hKE, hAE, RingHom.comp_apply, RingHom.comp_apply]
    exact congrArg (algebraMap ↥C.functionField N) (algebraMap_ordBase_baseField k C u x)
  haveI hIsFr : IsFractionRing ↥(C.ordBase u) ↥(baseField C u) :=
    Work.KeyLemma.Curve.instIsFractionRingOrdBaseBaseField k C u
  haveI hC'fracI : IsFractionRing ↥(integralClosure ↥(C.ordBase u) N) N := hC'frac
  -- ## the algebra structures on `R' = (C')_P`
  letI hRalgC : Algebra ↥(integralClosure ↥(C.ordBase u) N) (Localization.AtPrime P) :=
    inferInstance
  letI hRalgk : Algebra k (Localization.AtPrime P) :=
    (((algebraMap ↥(integralClosure ↥(C.ordBase u) N) (Localization.AtPrime P)).comp
        (algebraMap ↥(C.ordBase u) ↥(integralClosure ↥(C.ordBase u) N))).comp
      (algebraMap k ↥(C.ordBase u))).toAlgebra
  haveI hAtPrime : IsLocalization.AtPrime (Localization.AtPrime P) P := inferInstance
  have hunit : ∀ y : P.primeCompl,
      IsUnit (algebraMap ↥(integralClosure ↥(C.ordBase u) N) N
        (y : ↥(integralClosure ↥(C.ordBase u) N))) := by
    intro y
    refine IsUnit.mk0 _ (fun h0 => ?_)
    have hy0 : (y : ↥(integralClosure ↥(C.ordBase u) N)) ≠ 0 := by
      intro hy
      have : (y : ↥(integralClosure ↥(C.ordBase u) N)) ∈ P := hy ▸ Submodule.zero_mem _
      exact y.2 this
    exact hy0 ((IsFractionRing.injective ↥(integralClosure ↥(C.ordBase u) N) N)
      (by rw [h0, map_zero]))
  let phi : Localization.AtPrime P →+* N :=
    IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P)
      (g := algebraMap ↥(integralClosure ↥(C.ordBase u) N) N) hunit
  have hphi : ∀ x : ↥(integralClosure ↥(C.ordBase u) N),
      phi (algebraMap ↥(integralClosure ↥(C.ordBase u) N) (Localization.AtPrime P) x)
        = algebraMap ↥(integralClosure ↥(C.ordBase u) N) N x :=
    fun x => IsLocalization.lift_eq hunit x
  letI hRalgN : Algebra (Localization.AtPrime P) N := phi.toAlgebra
  haveI hSTCN : IsScalarTower ↥(integralClosure ↥(C.ordBase u) N)
      (Localization.AtPrime P) N :=
    IsScalarTower.of_algebraMap_eq (fun x => (hphi x).symm)
  haveI hSTkN : IsScalarTower k (Localization.AtPrime P) N := by
    refine IsScalarTower.of_algebraMap_eq (R := k) (S := Localization.AtPrime P) (A := N) ?_
    intro x
    show algebraMap k N x = phi (algebraMap k (Localization.AtPrime P) x)
    rw [show algebraMap k (Localization.AtPrime P) x
        = algebraMap ↥(integralClosure ↥(C.ordBase u) N) (Localization.AtPrime P)
            (algebraMap ↥(C.ordBase u) ↥(integralClosure ↥(C.ordBase u) N)
              (algebraMap k ↥(C.ordBase u) x)) from rfl]
    rw [hphi, ← IsScalarTower.algebraMap_apply ↥(C.ordBase u)
        ↥(integralClosure ↥(C.ordBase u) N) N (algebraMap k ↥(C.ordBase u) x),
      hAE, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply k ↥(C.ordBase u) ↥C.functionField x]
    exact hkE x
  haveI hFrR : IsFractionRing (Localization.AtPrime P) N :=
    IsFractionRing.isFractionRing_of_isLocalization (P.primeCompl)
      (Localization.AtPrime P) N (by
        intro y hy
        rw [mem_nonZeroDivisors_iff_ne_zero]
        intro h0
        exact hy (h0 ▸ Submodule.zero_mem _))
  -- ## `R'` is a DVR
  haveI hDedI : IsDedekindDomain ↥(integralClosure ↥(C.ordBase u) N) := hDed
  have hodIdeal_ne : C.ordIdeal u ≠ ⊥ := by
    intro h1
    have h2 : (⟨u, Algebra.subset_adjoin (Set.mem_singleton u)⟩ : C.ordBase u) = 0 := by
      have h3 : Ideal.span {(⟨u, Algebra.subset_adjoin (Set.mem_singleton u)⟩ : C.ordBase u)}
          = (⊥ : Ideal (C.ordBase u)) := by rw [← h1]
      exact Ideal.span_singleton_eq_bot.mp h3
    exact hu0 (Subtype.ext_iff.mp h2)
  have hPne : P ≠ ⊥ := by
    intro h0
    refine hodIdeal_ne ?_
    rw [← hPunder, h0, hunderbot]
  haveI hPneI : P ≠ ⊥ := hPne
  haveI hDVR : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      ↥(integralClosure ↥(C.ordBase u) N) hPne (Localization.AtPrime P)
  -- ## the branch sum
  obtain ⟨ρraw, e, hρover, hρgen, hρcl⟩ :=
    branch_sum (C := C) (h := u) hut f (N := N) hKE hAE P s hs
  have hgen : Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime P) N)) ≫ ρraw
      = genericSum (C := C) (h := h) (N := N) f := hρgen.trans hg
  -- ## conclude with separatedness of `A`
  let ρ : Work.SpecLin.RPt A (Localization.AtPrime P) := Over.homMk ρraw hρover
  let c₀ : Work.SpecLin.RPt A k := Over.homMk (Pt.leftHom c) (by
    show Pt.leftHom c ≫ A.hom = Spec.map (CommRingCat.ofHom (algebraMap k k))
    rw [Pt.leftHom_comp c, ← Spec.map_id (CommRingCat.of k)]
    congr 1)
  have hc₀ : c₀.left = c.leftHom := rfl
  have hρ1 : Work.SpecLin.RPt.map (IsScalarTower.toAlgHom k (Localization.AtPrime P) N) ρ
      = Work.SpecLin.RPt.map (IsScalarTower.toAlgHom k k N) c₀ := by
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime P) N)) ≫ ρraw
      = Spec.map (CommRingCat.ofHom (algebraMap k N)) ≫ c.leftHom
    rw [hgen, hc]
  exact sumOfPoints_eq_of_branch C f ρ c c₀ hc₀ e hρ1 hρcl

end Work.KeyLemma.Curve
