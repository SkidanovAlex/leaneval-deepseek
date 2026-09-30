/-
# The sections of the generic fibre of a chart are the localisation of the relative chart

For a curve `C` over a field `K`, a `K`-valuation ring `R` with fraction field `F = Frac R`, and
an affine open chart `W ⊆ C` with coordinate ring `A = Γ(C,W)`, let

* `B = A ⊗_K R` be the coordinate ring of the relative chart `W ×_K Spec R`
  (`Work.SpecLin.Core.chartTensor`), and
* `S = Γ(C_F, W_F)` the coordinate ring of the chart `W_F` of the generic fibre `C_F`
  (`W_F = C.bcOpens F W`, `S` is `A ⊗_K F` under `Curve.BCSquare.sectionsLift`).

This file proves that the `K`-algebra map `B → S` of `Work.SpecLin.Alt.chartTensorSectionsMap`
exhibits `S` as the localisation of the relative chart `B` at the image of the non-zero divisors
of `R`:

`IsLocalization ((nonZeroDivisors R).map includeRight) Γ(C_F, W_F)`.

The proof is the general localisation statement for a tensor product: `A ⊗_K F` is the
localisation of `A ⊗_K R` at the non-zero divisors of `R`
(`IsLocalization.tensorProduct_tensorProduct_right`), because `F = (nonZeroDivisors R)⁻¹R`
(`IsFractionRing`), transported along the ring isomorphism `sectionsLift : A ⊗_K F ≅ Γ(C_F, W_F)`
(an isomorphism since `sectionsLift` underlies an isomorphism of affine schemes) using
`IsLocalization.isLocalization_of_algEquiv`.
-/
import Mathlib
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.CurveBasics.Curve.BCSquare.SectionsTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Alt

open Work.CurveBasics in
/-- **`Curve.BCSquare.sectionsLift` is bijective**: it is the ring hom underlying the
isomorphism `Spec Γ(C', S.π ⁻¹ᵁ W) ≅ Spec (Γ(C,W) ⊗[k] F)` which defines it.  Indeed
`Spec.preimage` of the isomorphism `u` is a two-sided inverse, since `Spec.map` is an
equivalence on such hom sets (`Spec.map_preimage`). -/
theorem sectionsLift_bijective {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (W : C.left.Opens)
    (hW : IsAffineOpen W) :
    Function.Bijective (Curve.BCSquare.sectionsLift S W hW) := by
  unfold Curve.BCSquare.sectionsLift
  set u := ((Curve.BCSquare.isPullback_spec_preimage S W hW).isoPullback ≪≫
    pullbackSpecIso k Γ(C.left, W) F) with hu
  -- `Spec.preimage u.inv` is a left inverse: `u.hom ≫ u.inv = 𝟙` pulls back to
  -- `Spec.preimage u.hom ≫ Spec.preimage u.inv = 𝟙`
  have hleft : Function.LeftInverse (fun z => (Spec.preimage u.inv).hom z)
      (fun z => (Spec.preimage u.hom).hom z) := by
    intro z
    have hid : (Spec.preimage u.hom ≫ Spec.preimage u.inv :
        CommRingCat.of (Γ(C.left, W) ⊗[k] F) ⟶ CommRingCat.of (Γ(C.left, W) ⊗[k] F)) =
        𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id]
      exact Iso.inv_hom_id u
    exact congrArg (fun (φ : CommRingCat.of (Γ(C.left, W) ⊗[k] F) ⟶
      CommRingCat.of (Γ(C.left, W) ⊗[k] F)) => φ.hom z) hid
  -- `Spec.preimage u.inv` is a right inverse, from `u.inv ≫ u.hom = 𝟙`
  have hright : Function.RightInverse (fun z => (Spec.preimage u.inv).hom z)
      (fun z => (Spec.preimage u.hom).hom z) := by
    intro z
    have hid : (Spec.preimage u.inv ≫ Spec.preimage u.hom :
        CommRingCat.of Γ(C'.left, S.π ⁻¹ᵁ W) ⟶ CommRingCat.of Γ(C'.left, S.π ⁻¹ᵁ W)) =
        𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id]
      exact Iso.hom_inv_id u
    exact congrArg (fun (φ : CommRingCat.of Γ(C'.left, S.π ⁻¹ᵁ W) ⟶
      CommRingCat.of Γ(C'.left, S.π ⁻¹ᵁ W)) => φ.hom z) hid
  exact ⟨hleft.injective, hright.surjective⟩

open Work.CurveBasics in
/-- **The chart dictionary, localisation form.**  For a curve `C` over a field `K`, a `K`-valuation
ring `R` and an affine open chart `W ⊆ C`, the sections `Γ(C_F, W_F)` of the chart `W_F` of the
generic fibre are the localisation of the relative chart `B = Γ(C,W) ⊗_K R` at the image of the
non-zero divisors of `R` (so that `B`-elements whose `R`-content is non-zero already become
invertible). -/
theorem isLocalization_chartTensorSectionsMap {K : Type _} [Field K]
    {C : Work.CurveBasics.Curve K} (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W] :
    letI : Algebra (Work.SpecLin.Core.chartTensor R W)
      ((C.baseChange (FractionRing R)).left.presheaf.obj (Opposite.op (C.bcOpens (FractionRing R) W))) :=
      (Work.SpecLin.Alt.chartTensorSectionsMap R W hW).toAlgebra
    IsLocalization
      ((nonZeroDivisors R).map (Algebra.TensorProduct.includeRight (R := K)
        (A := C.left.presheaf.obj (Opposite.op W)) (B := R)))
      ((C.baseChange (FractionRing R)).left.presheaf.obj (Opposite.op (C.bcOpens (FractionRing R) W))) := by
  -- Step 1: the algebra structure on `A ⊗_K F` making it the base change `B ⊗_R F` of `B`.
  letI : Algebra (Γ(C.left, W) ⊗[K] R) (Γ(C.left, W) ⊗[K] FractionRing R) :=
    (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left, W))
      (IsScalarTower.toAlgHom K R (FractionRing R))).toAlgebra
  haveI hST : IsScalarTower Γ(C.left, W) (Γ(C.left, W) ⊗[K] R)
      (Γ(C.left, W) ⊗[K] FractionRing R) := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.map_tmul]
  -- the two algebra structures agree on the right tensor factor
  have H : (algebraMap (Γ(C.left, W) ⊗[K] R) (Γ(C.left, W) ⊗[K] FractionRing R)).comp
      Algebra.TensorProduct.includeRight.toRingHom
      = Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap R (FractionRing R)) := by
    ext r
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul]
  -- Step 2: `A ⊗_K F` is the localisation of `A ⊗_K R` at the image of `nonZeroDivisors R`
  haveI hT : IsLocalization ((nonZeroDivisors R).map (Algebra.TensorProduct.includeRight (R := K)
      (A := Γ(C.left, W)) (B := R))) (Γ(C.left, W) ⊗[K] FractionRing R) :=
    IsLocalization.tensorProduct_tensorProduct_right (R := K) (S := Γ(C.left, W))
      (A := R) (M := nonZeroDivisors R) (B := FractionRing R) H
  -- Step 3: the algebra structure on the chart `W_F` of the generic fibre
  letI : Algebra (Γ(C.left, W) ⊗[K] R)
      ((C.baseChange (FractionRing R)).left.presheaf.obj (Opposite.op (C.bcOpens (FractionRing R) W))) :=
    (Work.SpecLin.Alt.chartTensorSectionsMap R W hW).toAlgebra
  -- `sectionsLift : A ⊗_K F ≅ Γ(C_F, W_F)` is an isomorphism of `B`-algebras, because both
  -- algebra structures are `sectionsLift ∘ (map id (R → F))`.
  have hbij : Function.Bijective
      (Curve.BCSquare.sectionsLift (Curve.bcSquare C (FractionRing R)) W hW) :=
    sectionsLift_bijective (Curve.bcSquare C (FractionRing R)) W hW
  refine IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective
      (Curve.BCSquare.sectionsLift (Curve.bcSquare C (FractionRing R)) W hW) hbij) ?_)
  intro b
  show Curve.BCSquare.sectionsLift (Curve.bcSquare C (FractionRing R)) W hW
      (algebraMap (Γ(C.left, W) ⊗[K] R) (Γ(C.left, W) ⊗[K] FractionRing R) b) = _
  rw [RingHom.algebraMap_toAlgebra]
  rfl

end Work.SpecLin.Alt
