/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Normality of smooth algebras over a field

The main theorem of this file is `Work.Normality.isIntegrallyClosed_of_smooth`: a domain which
is standard smooth of relative dimension `n` over a field is an integrally closed ring.  This is
the classical theorem "a smooth algebra over a field is regular, hence normal", proved here by
the standard reduction:

* a submersive presentation `SubmersivePresentation K A ι σ` exhibits `A` as a quotient of
  `K[X_ι]` by relations indexed by `σ`, with invertible Jacobian;
* let `κ := (Set.range Pr.map)ᶜ` be the set of generators *not* occurring among the relations and
  let `P₀ := MvPolynomial κ K`; then the natural map `A ⊗[P₀] Ω[P₀⁄K] → Ω[A⁄K]` is *bijective*
  (`Work.Normality.bijective_mapBaseChange_complement`), because it carries the standard basis
  `{1 ⊗ dX_k}` onto the basis `SubmersivePresentation.basisKaehler` of `Ω[A⁄K]`;
* the Jacobi–Zariski sequence then shows that `A` is formally smooth over `P₀`
  (`Work.Normality.formallySmooth_of_bijective_mapBaseChange`), and `A` is of finite presentation
  over `P₀` (the standard smooth presentation of `A` over `K` is finitely generated), so `A` is
  *smooth* over `P₀`; since `Ω[A⁄P₀] = 0` it is in fact étale over `P₀`;
* `P₀` is a polynomial ring over a field, hence a UFD, hence integrally closed, and Mathlib's
  `TensorProduct.toIntegralClosure_bijective_of_smooth` then shows that `A` is integrally closed
  in `A ⊗[P₀] FractionRing P₀`
  (`Work.Normality.isIntegrallyClosedIn_tensorProduct_fractionRing`);
* that ring is a domain (`Work.Normality.isDomain_tensorProduct_fractionRing`) — using flatness of
  `A` over `P₀` — and étale over the field `FractionRing P₀`, so it is a field
  (`Work.Normality.isField_of_etale_of_isDomain`), and finally
  `IsIntegrallyClosed.of_isIntegrallyClosedIn` concludes.

The scheme-theoretic consequences (`HasIntegrallyClosedStalks`) are collected in
`Work.Normality.Scheme`.
-/
import Mathlib
import Submission.Work.Normality.Basic
import Submission.Work.Normality.bijective_mapBaseChange_complement
import Submission.Work.Normality.formallySmooth_of_bijective_mapBaseChange
import Submission.Work.Normality.isIntegrallyClosedIn_tensorProduct_fractionRing
import Submission.Work.Normality.injective_algebraMap_tensorProduct_fractionRing
import Submission.Work.Normality.isDomain_tensorProduct_fractionRing
import Submission.Work.Normality.isField_of_etale_of_isDomain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Work.Normality

noncomputable section

/-- A domain which is integrally closed in a field containing it is integrally closed. -/
theorem isIntegrallyClosed_of_isIntegrallyClosedIn_field {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] (hfield : IsField B)
    (hinj : Function.Injective (algebraMap A B)) (hB : IsIntegrallyClosedIn A B) :
    IsIntegrallyClosed A := by
  letI : Field B := hfield.toField
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn A B

/-- **A domain which is standard smooth of relative dimension `n` over a field is integrally
closed.**  This is the algebraic core of the area: it is the statement that a smooth algebra
over a field is normal, in the form needed for the stalks of `Cⁿ` and `Symⁿ C`. -/
theorem isIntegrallyClosed_of_smooth {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] {n : ℕ} [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    IsIntegrallyClosed A := by
  obtain ⟨ι, σ, hσfin, _hιfin, Pr, _hdim⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := n) (R := K) (S := A)
  haveI : Finite σ := hσfin
  -- `P₀` is the polynomial ring on the generators which do not occur among the relations
  let P₀ := MvPolynomial ↥(Set.range Pr.map)ᶜ K
  let φ : P₀ →ₐ[K] A := MvPolynomial.aeval fun k => Pr.val k.1
  letI : Algebra P₀ A := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K P₀ A :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have hφ : ∀ k : ↥(Set.range Pr.map)ᶜ,
      algebraMap P₀ A (MvPolynomial.X k) = Pr.val k.1 := fun k => by
    rw [RingHom.algebraMap_toAlgebra]
    exact MvPolynomial.aeval_X _ k
  -- the Kähler differentials of `A` over `P₀` are the base change of those of `P₀` over `K`
  have hbij : Function.Bijective (KaehlerDifferential.mapBaseChange K P₀ A) :=
    bijective_mapBaseChange_complement (K := K) (A := A) Pr hφ
  haveI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Algebra.FormallySmooth K A := inferInstance
  haveI : Algebra.FormallySmooth P₀ A := formallySmooth_of_bijective_mapBaseChange hbij
  haveI : Algebra.FiniteType P₀ A :=
    Algebra.FiniteType.of_restrictScalars_finiteType K P₀ A
  haveI : Algebra.FinitePresentation P₀ A :=
    (Algebra.FinitePresentation.of_finiteType (R := P₀) (A := A)).mp ‹Algebra.FiniteType P₀ A›
  haveI : Algebra.Smooth P₀ A := ⟨‹Algebra.FormallySmooth P₀ A›, ‹Algebra.FinitePresentation P₀ A›⟩
  haveI : Module.Flat P₀ A := Algebra.Smooth.flat P₀ A
  -- `Ω[A⁄P₀] = 0`, so `A` is étale over `P₀`
  have hker : LinearMap.ker (KaehlerDifferential.map K P₀ A A) = ⊤ := by
    rw [(KaehlerDifferential.exact_mapBaseChange_map K P₀ A).linearMap_ker_eq,
      LinearMap.range_eq_top.mpr hbij.2]
  have hsub : Subsingleton Ω[A⁄P₀] := ⟨fun x y => by
    obtain ⟨z, rfl⟩ := KaehlerDifferential.map_surjective K P₀ A x
    obtain ⟨w, rfl⟩ := KaehlerDifferential.map_surjective K P₀ A y
    have hz : KaehlerDifferential.map K P₀ A A z = 0 := by
      rw [← LinearMap.mem_ker, hker]; trivial
    have hw : KaehlerDifferential.map K P₀ A A w = 0 := by
      rw [← LinearMap.mem_ker, hker]; trivial
    rw [hz, hw]⟩
  haveI : Algebra.FormallyUnramified P₀ A := Algebra.FormallyUnramified.mk hsub
  haveI : Algebra.Etale P₀ A :=
    Algebra.Etale.iff_formallyUnramified_and_smooth.mpr
      ⟨‹Algebra.FormallyUnramified P₀ A›, ‹Algebra.Smooth P₀ A›⟩
  -- base change to the fraction field of `P₀`
  haveI : IsIntegrallyClosed P₀ := inferInstance
  let L := FractionRing P₀
  let B := TensorProduct P₀ A L
  have hB : IsIntegrallyClosedIn A B :=
    isIntegrallyClosedIn_tensorProduct_fractionRing (P := P₀) (A := A)
  have hinj : Function.Injective (algebraMap A B) :=
    injective_algebraMap_tensorProduct_fractionRing (P := P₀) (A := A)
  have hdom : IsDomain B := isDomain_tensorProduct_fractionRing (P := P₀) (A := A)
  -- `B` is étale over the field `L`: transfer along the swap isomorphism.  The `L`-algebra
  -- structure on `B` (given by the *second* factor) is only introduced locally, so that it does
  -- not interfere with the (global) `A`-algebra structure used below.
  have hfield : IsField B := by
    letI : Algebra L B := Algebra.TensorProduct.rightAlgebra
    let e : B ≃ₐ[L] TensorProduct P₀ L A :=
      { (Algebra.TensorProduct.comm P₀ A L) with
        commutes' := fun l => by
          show (Algebra.TensorProduct.comm P₀ A L) ((algebraMap L B) l) = _
          rw [Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.comm_tmul,
            Algebra.TensorProduct.algebraMap_apply]
          simp }
    haveI : Algebra.Etale L (TensorProduct P₀ L A) := Algebra.Etale.baseChange P₀ A L
    haveI : Algebra.Etale L B := Algebra.Etale.of_equiv e.symm
    exact isField_of_etale_of_isDomain (L := L) (B := B)
  exact isIntegrallyClosed_of_isIntegrallyClosedIn_field hfield hinj hB

/-- A domain which is standard smooth (of any relative dimension) over a field is integrally
closed. -/
theorem isIntegrallyClosed_of_isStandardSmooth {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.IsStandardSmooth K A] : IsIntegrallyClosed A := by
  obtain ⟨ι, σ, hσ, _hι, ⟨Pr⟩⟩ := Algebra.IsStandardSmooth.out (R := K) (S := A)
  haveI : Finite σ := hσ
  haveI : Algebra.IsStandardSmoothOfRelativeDimension Pr.dimension K A :=
    Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension Pr rfl
  exact isIntegrallyClosed_of_smooth (K := K) (A := A) (n := Pr.dimension)

end

end Work.Normality
