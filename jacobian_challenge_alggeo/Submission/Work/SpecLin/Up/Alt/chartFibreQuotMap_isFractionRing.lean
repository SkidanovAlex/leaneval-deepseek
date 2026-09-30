/-
# Namespace mirror of `Work.SpecLin.Alt.chartFibreQuotMap_isFractionRing`

This file is an exact copy of `Submission/Work/SpecLin/Alt/chartFibreQuotMap_isFractionRing.lean` (module `Work.SpecLin.Alt.chartFibreQuotMap_isFractionRing`), changed in exactly three ways:

* a `namespace Up` / `end Up` pair is inserted immediately inside the file's own namespace, so
  that every declaration `Work.SpecLin.<Area>.<x>` of the original appears here as
  `Work.SpecLin.<Area>.Up.<x>` (this avoids a name clash with the original, which cannot be
  removed: the original is part of the shared library);
* references to declarations *of the mirrored modules* are rewritten accordingly (full and
  area-relative forms), and imports of those modules point at their mirrors;
* an import of `Core/linEquiv_of_sections_of_chart.lean` (the module that *states* the
  affine-chart theorem) is replaced by an import of the upstream vocabulary module
  `Core/chartVocab.lean`, which declares the same chart algebra under the same names.

The point of the mirror is to break the import cycle
`vocabulary -> statement -> ... -> proof modules -> vocabulary`: the proof modules used to take
their vocabulary from the module that states the theorem, and this made a proof of that theorem
unreachable.  The mathematics is unchanged: the mirror is a verbatim copy of verified code.

The statements of the mirrored theorems mention only names that are *upstream* of the mirror, so
`Work.SpecLin.Core.Up.chartSpecialisation` (module
`Submission.Work.SpecLin.Up.Core.chartSpecialisation`) has literally the statement of
`Work.SpecLin.Core.linEquiv_of_sections_of_chart`, which is proved from it.
-/
/-
# The special fibre of the chart dictionary: `K(C_κ)` is the fraction field of `B ⧸ P`

For a curve `C` over a field `K`, a `K`-valuation ring `R` (`κ = R ⧸ m_R` its residue field) and
an affine chart `W ⊆ C` with coordinate ring `A = Γ(C, W)`, the relative chart is
`B = A ⊗_K R`, its "special fibre prime" is `P = m_R · B = chartFibrePrime R W`, and the
quotient `B ⧸ P ≅ A ⊗_K κ = Γ(C_κ, W_κ)` is the coordinate ring of the affine chart of the
special fibre (`Work.SpecLin.Core.chartFibreQuotEquiv`).

This file proves that the reduction map of the chart dictionary,
`Work.SpecLin.Alt.Up.chartFibreQuotMap : B ⧸ P → K(C_κ)`, exhibits the function field of the
special fibre as the *fraction field* of `B ⧸ P`, i.e.

`IsFractionRing (B ⧸ P) K(C_κ)`.

The proof is the standard "localisation of an affine chart" argument, transported along the two
isomorphisms that make up the dictionary:

* `chartFibreQuotEquiv : B ⧸ P ≃+* A ⊗_K κ` (the special fibre of the tensor product),
* `sectionsLift : A ⊗_K κ ≃+* Γ(C_κ, W_κ)` (the sections of the affine chart of the base
  change; `sectionsLift` is injective by
  `Work.CurveBasics.Curve.BCSquare.sectionsLift_injective` and surjective by
  `sectionsLift_surjective` proved below),
* `IsFractionRing Γ(C_κ, W_κ) K(C_κ)` for a nonempty affine open of an integral scheme
  (`Work.SpecLin.Alt.isFractionRing_functionField` in `chartField.lean`).

The only point that has to be checked by hand is that the two descriptions of the quotient map
`B ⧸ P → K(C_κ)` agree: the reduction map of the chart dictionary is, on `B`, the composite

`B → A ⊗_K κ --sectionsLift--> Γ(C_κ, W_κ) → K(C_κ)`

(`chartFibreQuotEquiv_mk`), which is what makes the fraction-ring structure transfer.

The target statement is the special-fibre counterpart of
`Work.SpecLin.Alt.Up.chartTensorMap_isFractionRing` (generic fibre).
-/
import Mathlib
import Submission.Work.SpecLin.Up.Alt.chartMap
import Submission.Work.CurveBasics.Curve.BCSquare.SectionsTensor
import Submission.Work.SpecLin.Core.chartVocab
import Submission.Work.SpecLin.Alt.chartField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Alt
namespace Up

/-! ## `sectionsLift` is bijective -/

open Work.CurveBasics in
/-- **Surjectivity of `sectionsLift`.**  The structural ring hom
`Work.CurveBasics.Curve.BCSquare.sectionsLift S W hW : Γ(C,W) ⊗[k] F →+* Γ(C', S.π ⁻¹ᵁ W)` is
the underlying ring hom of an isomorphism of schemes (`Spec.preimage` of the comparison
isomorphism of `isPullback_spec_preimage`), hence surjective.  Injectivity is
`Work.CurveBasics.Curve.BCSquare.sectionsLift_injective`. -/
private theorem sectionsLift_surjective {k : Type u} [Field k] {F : Type u} [Field F]
    [Algebra k F] {C : Work.CurveBasics.Curve k} {C' : Work.CurveBasics.Curve F}
    (S : Work.CurveBasics.Curve.BCSquare C C') (W : C.left.Opens)
    (hW : IsAffineOpen W) :
    Function.Surjective (Work.CurveBasics.Curve.BCSquare.sectionsLift S W hW) := by
  set u := (Work.CurveBasics.Curve.BCSquare.isPullback_spec_preimage S W hW).isoPullback
    ≪≫ pullbackSpecIso k Γ(C.left, W) F with hu
  have hid : (Spec.preimage u.inv ≫ Spec.preimage u.hom :
      Γ(C'.left, S.π ⁻¹ᵁ W) ⟶ Γ(C'.left, S.π ⁻¹ᵁ W)) = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id]
    exact Iso.hom_inv_id u
  intro z
  exact ⟨(Spec.preimage u.inv).hom z,
    congrArg (fun (φ : Γ(C'.left, S.π ⁻¹ᵁ W) ⟶ Γ(C'.left, S.π ⁻¹ᵁ W)) => φ.hom z) hid⟩

open Work.CurveBasics in
/-- `sectionsLift` is bijective. -/
private theorem sectionsLift_bijective {k : Type u} [Field k] {F : Type u} [Field F]
    [Algebra k F] {C : Work.CurveBasics.Curve k} {C' : Work.CurveBasics.Curve F}
    (S : Work.CurveBasics.Curve.BCSquare C C') (W : C.left.Opens)
    (hW : IsAffineOpen W) :
    Function.Bijective (Work.CurveBasics.Curve.BCSquare.sectionsLift S W hW) :=
  ⟨Work.CurveBasics.Curve.BCSquare.sectionsLift_injective S W hW,
    sectionsLift_surjective S W hW⟩

/-! ## The fraction ring structure on `A ⊗_K κ` -/

open Work.CurveBasics in
/-- **The sections of the affine chart of the special fibre form a fraction ring.**  With the
algebra structure on `A ⊗_K κ` induced by the composite
`A ⊗_K κ → Γ(C_κ, S.π ⁻¹ᵁ W) → K(C_κ)` (`sectionsLift` followed by the germ at the generic
point), the tensor product `A ⊗_K κ` is a fraction ring for the function field `K(C_κ)`: this is
`IsFractionRing Γ(C_κ, S.π ⁻¹ᵁ W) K(C_κ)` (`isFractionRing_functionField`, as `S.π ⁻¹ᵁ W ⊆ C_κ`
is a nonempty affine open of an integral scheme) transported along the ring isomorphism
`sectionsLift`. -/
private theorem isFractionRing_chartTensor_residue {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K} (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    letI : Algebra (Γ(C.left, W) ⊗[K] IsLocalRing.ResidueField R)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
      ((Curve.germToFunctionField (C.baseChange (IsLocalRing.ResidueField R))
        ((Curve.bcSquare C (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W)).hom.comp
        (Curve.BCSquare.sectionsLift (Curve.bcSquare C (IsLocalRing.ResidueField R)) W
          hW)).toAlgebra
    IsFractionRing (Γ(C.left, W) ⊗[K] IsLocalRing.ResidueField R)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField := by
  letI : Algebra (Γ(C.left, W) ⊗[K] IsLocalRing.ResidueField R)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
      ((Curve.germToFunctionField (C.baseChange (IsLocalRing.ResidueField R))
        ((Curve.bcSquare C (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W)).hom.comp
        (Curve.BCSquare.sectionsLift (Curve.bcSquare C (IsLocalRing.ResidueField R)) W
          hW)).toAlgebra
  have hV : Nonempty ((Curve.bcSquare C (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W) :=
    Curve.BCSquare.instNonemptyPreimage _ W
  have haff : IsAffineOpen ((Curve.bcSquare C (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W) :=
    Curve.BCSquare.isAffineOpen_preimage _ W hW
  haveI hfr : IsFractionRing Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
      (Curve.bcSquare C (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
    Work.SpecLin.Alt.isFractionRing_functionField _ haff
  exact IsFractionRing.of_ringEquiv_left
    (RingEquiv.ofBijective
      (Curve.BCSquare.sectionsLift (Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW)
      (sectionsLift_bijective _ W hW))
    (fun x => rfl)

/-! ## The two descriptions of the reduction map agree -/

open Work.CurveBasics in
/-- **The fibre-quotient dictionary.**  The ring isomorphism `B ⧸ P ≃+* A ⊗_K κ` of the chart
dictionary (`Work.SpecLin.Core.chartFibreQuotEquiv`) is, on the class of an element of
`B = A ⊗_K R`, the natural reduction of the second tensor factor
`A ⊗_K R → A ⊗_K κ`, `a ⊗ r ↦ a ⊗ (r mod m_R)`. -/
private theorem chartFibreQuotEquiv_mk {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (b : Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W) :
    Work.SpecLin.Core.chartFibreQuotEquiv (K:=K) (C:=C) R W
        (Ideal.Quotient.mk (Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W) b)
      = Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
          (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) b := by
  refine TensorProduct.inductionOn (motive := fun b =>
    Work.SpecLin.Core.chartFibreQuotEquiv (K:=K) (C:=C) R W
        (Ideal.Quotient.mk (Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W) b)
      = Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
          (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) b) b ?_ ?_
  · intro a t
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    show (Algebra.TensorProduct.tensorQuotientEquiv (R := K) K R Γ(C.left, W)
        (IsLocalRing.maximalIdeal R)).symm
        (Ideal.Quotient.mk _ (a ⊗ₜ[K] t))
      = a ⊗ₜ[K] (algebraMap R (IsLocalRing.ResidueField R)) t
    rw [Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul]
    rfl
  · intro x y hx hy
    simp only [map_add]
    rw [hx, hy]

/-! ## The target -/

theorem chartFibreQuotMap_isFractionRing {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W] :
    letI : Algebra (Work.SpecLin.Core.chartTensor R W ⧸
        Work.SpecLin.Core.chartFibrePrime R W)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
      (Work.SpecLin.Alt.Up.chartFibreQuotMap R W hW).toAlgebra
    IsFractionRing (Work.SpecLin.Core.chartTensor R W ⧸
        Work.SpecLin.Core.chartFibrePrime R W)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField := by
  letI : Algebra (Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W ⧸
      Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
      (Work.SpecLin.Alt.Up.chartFibreQuotMap R W hW).toAlgebra
  letI : Algebra (Γ(C.left, W) ⊗[K] IsLocalRing.ResidueField R)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
      ((Work.CurveBasics.Curve.germToFunctionField (C.baseChange (IsLocalRing.ResidueField R))
        ((Work.CurveBasics.Curve.bcSquare C (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W)).hom.comp
        (Work.CurveBasics.Curve.BCSquare.sectionsLift
          (Work.CurveBasics.Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW)).toAlgebra
  haveI hmid : IsFractionRing (Γ(C.left, W) ⊗[K] IsLocalRing.ResidueField R)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
    isFractionRing_chartTensor_residue R W hW
  refine IsFractionRing.of_ringEquiv_left
    (Work.SpecLin.Core.chartFibreQuotEquiv (K:=K) (C:=C) R W) ?_
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [chartFibreQuotEquiv_mk R W hW b]
  simp only [RingHom.algebraMap_toAlgebra]
  rfl

end Up
end Work.SpecLin.Alt

