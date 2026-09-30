/-
# The chart dictionary is a fraction-ring statement (generic fibre)

For a curve `C` over a field `K`, a `K`-valuation ring `R` with fraction field `F = Frac R`, and
an affine open chart `W ⊆ C` with coordinate ring `A = Γ(C,W)`, the "chart dictionary" map

`chartTensorMap : B = A ⊗_K R ⟶ K(C_F)`

(`B` the coordinate ring of the relative chart `W ×_K Spec R`, `K(C_F)` the function field of
the generic fibre) exhibits `K(C_F)` as the fraction field of `B`.

The proof decomposes the map as

`B --φG--> G = A ⊗_K F --e--> S = Γ(C_F, W_F) --germ--> K(C_F)`,

where

* `φG` is injective (`K` is a field, so `A` is a flat, even free, `K`-module, and
  `R → F` is injective),
* `G` is a domain, because `S ≅ G` are the sections of the nonempty affine chart `W_F` of the
  geometrically integral curve `C_F` (`Curve.isDomain_tensor_sections`),
* `IsLocalization M' G` for `M'` the image of the non-zero divisors of `R` in `B`
  (`IsLocalization.tensorProduct_tensorProduct_right`),
* `IsFractionRing S K(C_F)` (`Alt.isFractionRing_functionField`), transported to `G` along the
  ring isomorphism `e` (an instance of the general fact that `K(C_F)` is the fraction field of
  `B[（nzds of R)⁻¹]`).

The last step is the transitivity of "fraction field": every element of `K(C_F)` is a quotient
of elements of `S`, and every element of `S` is a quotient of elements of `B` by units of `B`
(non-zero-divisors of `R`), so every element of `K(C_F)` is a quotient of elements of `B`.
-/
import Mathlib
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.CurveBasics.Curve.BCSquare.SectionsTensor
import Submission.Work.SpecLin.Alt.chartField
import Submission.Work.CurveBasics.Basic.isDomain_tensor_sections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open Work.CurveBasics

namespace Work.SpecLin.Alt

open Work.CurveBasics in
/-- **`Curve.BCSquare.sectionsLift` is surjective**: it is the ring hom underlying the
isomorphism `Spec Γ(C', S.π ⁻¹ᵁ W) ≅ Spec (Γ(C,W) ⊗[k] F)` used to define it. -/
theorem sectionsLift_surjective (k : Type u) [Field k] (F : Type u) [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (W : C.left.Opens)
    (hW : IsAffineOpen W) :
    Function.Surjective (Curve.BCSquare.sectionsLift S W hW) := by
  set p := (Curve.BCSquare.isPullback_spec_preimage S W hW).isoPullback ≪≫
    pullbackSpecIso k Γ(C.left, W) F with hp
  have hright : Function.RightInverse (fun z => (Spec.preimage p.inv).hom z)
      (fun z => (Spec.preimage p.hom).hom z) := by
    intro z
    have hid : (Spec.preimage p.inv ≫ Spec.preimage p.hom :
        CommRingCat.of (Γ(C'.left, S.π ⁻¹ᵁ W)) ⟶ CommRingCat.of (Γ(C'.left, S.π ⁻¹ᵁ W))) =
        𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id]
      exact Iso.hom_inv_id p
    exact congrArg (fun (φ : CommRingCat.of (Γ(C'.left, S.π ⁻¹ᵁ W)) ⟶
      CommRingCat.of (Γ(C'.left, S.π ⁻¹ᵁ W))) => φ.hom z) hid
  exact hright.surjective

theorem chartTensorMap_isFractionRing {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W] :
    letI : Algebra (Work.SpecLin.Core.chartTensor R W)
      (C.baseChange (FractionRing R)).functionField :=
      (Work.SpecLin.Alt.chartTensorMap R W hW).toAlgebra
    IsFractionRing (Work.SpecLin.Core.chartTensor R W)
      (C.baseChange (FractionRing R)).functionField := by
  letI : Algebra (Work.SpecLin.Core.chartTensor R W)
      (C.baseChange (FractionRing R)).functionField :=
      (Work.SpecLin.Alt.chartTensorMap R W hW).toAlgebra
  -- ## Abbreviations
  let Ac := Γ(C.left, W)
  let Fc := FractionRing R
  let Bc := Ac ⊗[K] R
  let Gc := Ac ⊗[K] Fc
  let Lf := (C.baseChange Fc).functionField
  let Sc := Γ((C.baseChange Fc).left, C.bcOpens Fc W)
  let φG : Bc →+* Gc :=
    (Algebra.TensorProduct.map (AlgHom.id K Ac) (IsScalarTower.toAlgHom K R Fc)).toRingHom
  let φS : Bc →+* Sc := (Curve.BCSquare.sectionsLift (Curve.bcSquare C Fc) W hW).comp φG
  let g : Sc →+* Lf := (Curve.germToFunctionField (C.baseChange Fc) (C.bcOpens Fc W)).hom
  letI : Algebra Bc Gc := φG.toAlgebra
  letI : Algebra Bc Sc := φS.toAlgebra
  -- the algebra maps are the ones we named
  have halgBL : (algebraMap Bc Lf) = (Work.SpecLin.Alt.chartTensorMap R W hW) := rfl
  have hchart : (Work.SpecLin.Alt.chartTensorMap R W hW) = g.comp φS := rfl
  have halgSL : (algebraMap Sc Lf) = g := rfl
  have halgBS : (algebraMap Bc Sc) = φS := rfl
  -- ## `Gc` is a domain and `φG` is injective
  haveI : IsDomain Gc := Work.CurveBasics.Curve.isDomain_tensor_sections C hW Fc
  have hφGinj : Function.Injective φG :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Ac)
      (f := (IsScalarTower.toAlgHom K R Fc).toLinearMap) (IsFractionRing.injective R Fc)
  -- ## `Gc` is the localization of `Bc` at the image of the non-zero divisors of `R`
  let M' : Submonoid Bc :=
    (nonZeroDivisors R).map (Algebra.TensorProduct.includeRight (R:=K) (A:=Ac) (B:=R))
  haveI hγ : IsLocalization M' Gc := by
    haveI hST : IsScalarTower Ac Bc Gc :=
      IsScalarTower.of_algebraMap_eq (fun a => by
        rw [show algebraMap Ac Bc a = a ⊗ₜ[K] (1:R) from rfl]
        show a ⊗ₜ[K] (1 : Fc) =
          (Algebra.TensorProduct.map (AlgHom.id K Ac) (IsScalarTower.toAlgHom K R Fc))
            (a ⊗ₜ[K] (1:R))
        rw [Algebra.TensorProduct.map_tmul]
        simp)
    have hH : (algebraMap Bc Gc).comp
        (Algebra.TensorProduct.includeRight (R:=K) (A:=Ac) (B:=R)).toRingHom
        = (Algebra.TensorProduct.includeRight (R:=K) (A:=Ac) (B:=Fc)).toRingHom.comp
            (algebraMap R Fc) := by
      ext r
      show (Algebra.TensorProduct.map (AlgHom.id K Ac) (IsScalarTower.toAlgHom K R Fc))
          ((1:Ac) ⊗ₜ[K] r) = (1:Ac) ⊗ₜ[K] algebraMap R Fc r
      rw [Algebra.TensorProduct.map_tmul]
      simp
    exact IsLocalization.tensorProduct_tensorProduct_right (R := K) (S := Ac) (A := R)
      (M := nonZeroDivisors R) (B := Fc) hH
  -- ## the ring isomorphism `Gc ≃+* Sc`
  let e : Gc ≃+* Sc :=
    RingEquiv.ofBijective (Curve.BCSquare.sectionsLift (Curve.bcSquare C Fc) W hW)
      ⟨Curve.BCSquare.sectionsLift_injective _ W hW, sectionsLift_surjective K Fc _ W hW⟩
  have hφSe : φS = e.toRingHom.comp φG := rfl
  -- ## the function field is the fraction field of `Sc`, hence of `Gc`
  haveI hSL : IsFractionRing Sc Lf :=
    isFractionRing_functionField (C.bcOpens Fc W)
      (Curve.BCSquare.isAffineOpen_preimage (Curve.bcSquare C Fc) W hW)
  haveI : IsDomain Sc := Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  have hginj : Function.Injective g :=
    Scheme.germToFunctionField_injective (C.baseChange Fc).left (C.bcOpens Fc W)
  have hφLinj : Function.Injective (algebraMap Bc Lf) := by
    rw [halgBL, hchart]
    exact hginj.comp (e.injective.comp hφGinj)
  haveI : FaithfulSMul Bc Lf := (faithfulSMul_iff_algebraMap_injective Bc Lf).mpr hφLinj
  -- the non-zero divisors of `R` become units of `K(C_F)`
  have hunit : ∀ b ∈ M', IsUnit (algebraMap Bc Lf b) := by
    intro b hb
    have h1 : IsUnit (algebraMap Bc Gc b) :=
      IsLocalization.map_units (M := M') (S := Gc) ⟨b, hb⟩
    have h3 : algebraMap Bc Lf b = g (e (algebraMap Bc Gc b)) := rfl
    rw [h3]
    exact (h1.map e.toRingHom).map g
  -- ## `K(C_F)` is the fraction field of `Bc`
  refine IsFractionRing.of_field Bc Lf (fun z => ?_)
  -- `z` is a quotient of elements of `Sc`
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (M := nonZeroDivisors Sc) (S := Lf) z
  -- and `s`, `t` are quotients of elements of `Bc` with denominators in `M'`
  obtain ⟨⟨xs, ys⟩, hys⟩ := IsLocalization.surj (M := M') (S := Gc) (e.symm s)
  obtain ⟨⟨xt, yt⟩, hyt⟩ := IsLocalization.surj (M := M') (S := Gc) (e.symm t)
  have h2s : (s : Sc) * φS (ys : Bc) = φS xs := by
    have h := congrArg e hys
    rwa [map_mul, RingEquiv.apply_symm_apply] at h
  have h2t : (t : Sc) * φS (yt : Bc) = φS xt := by
    have h := congrArg e hyt
    rwa [map_mul, RingEquiv.apply_symm_apply] at h
  have E1 : algebraMap Bc Lf (xs : Bc)
      = algebraMap Sc Lf (s : Sc) * algebraMap Bc Lf (ys : Bc) := by
    have h := congrArg g h2s.symm
    simp only [halgBL, hchart, halgSL, RingHom.comp_apply, map_mul] at h ⊢
    exact h
  have E2 : algebraMap Bc Lf (xt : Bc)
      = algebraMap Sc Lf (t : Sc) * algebraMap Bc Lf (yt : Bc) := by
    have h := congrArg g h2t.symm
    simp only [halgBL, hchart, halgSL, RingHom.comp_apply, map_mul] at h ⊢
    exact h
  have ht0 : algebraMap Sc Lf (t : Sc) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
  have hys0 : algebraMap Bc Lf (ys : Bc) ≠ 0 := (hunit ys.1 ys.2).ne_zero
  have hyt0 : algebraMap Bc Lf (yt : Bc) ≠ 0 := (hunit yt.1 yt.2).ne_zero
  have hxt0 : algebraMap Bc Lf (xt : Bc) ≠ 0 := by
    intro h0
    rw [E2] at h0
    exact mul_ne_zero ht0 hyt0 h0
  refine ⟨xs * yt, xt * ys, ?_⟩
  have hden : algebraMap Bc Lf (xt * ys) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hxt0 hys0
  rw [eq_div_iff hden, map_mul, map_mul, E2, E1, ← hst]
  ring

end Work.SpecLin.Alt
