import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.K3Inputs.Defs
import Submission.Work.K3Inputs.cylFieldAlgEquiv
import Submission.Work.K3Inputs.cylIsoPullbackAffineLine
import Submission.Work.CrauderKatz.residueField_genericPoint_resAlgEquiv
import Submission.Work.CY3Stab.Prod.isIntegral_wProd
import Submission.Work.Motivic.cInv_add_defs
import Submission.Work.LLink.Count

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.resAlgEquiv_genericPoint_wProd_one`

The generic point of the cylinder `𝔸¹ ×_𝕜 X` of an integral `𝕜`-scheme `X` has residue field
`κ(X)(t) = RatFunc κ(X)`, compatibly with the structure maps `𝕜 → κ(X)(t)`.

This is the `k = 1` case of the residue-field computation of the stabilisation that is used to
compare a `ResEquiv` of cylinder points with that of the base points: it identifies the residue
field of the generic point of the cylinder `𝔸¹ ×_𝕜 X` with the model `Work.K3Inputs.cylField 𝕜 X
= RatFunc κ(X)` of the function field of `X × ℙ¹`.

The proof is the composition of two delivered computations.

* `Work.CrauderKatz.residueField_genericPoint_resAlgEquiv` at `i = 𝟙` (packaged below as
  `resAlgEquiv_genericPoint_functionField`) computes the residue field of the generic point of an
  integral `𝕜`-scheme as its function field, `𝕜`-linearly;
* `Work.K3Inputs.cylFieldAlgEquiv` computes the function field of the fibre product
  `X ×_{Spec 𝕜} Spec 𝕜[t]` as `RatFunc κ(X)`, `𝕜`-linearly.

The only geometric plumbing is the identification of the cylinder point whose fibre product
`WProd 𝕜 X 1 = 𝔸¹ ×_{Spec 𝕜} X` (with the `𝔸¹`-leg *first*, the order fixed by
`Work.K3.baseChangeAlong`) with the shape `X ×_{Spec 𝕜} Spec 𝕜[t]` required by
`cylFieldAlgEquiv`, which is `Work.CY3Stab.Prod.exists_iso_wProd_one` below: the swap of the two
legs together with the identification `𝔸(Fin 1; Spec 𝕜) = Spec 𝕜[t]` of `𝔸¹` with the standard
affine line (`Work.K3Inputs.affine1_iso_specPolynomial`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-! ## 1. The cylinder `𝔸¹ ×_𝕜 X` as a fibre product of `X` with `Spec 𝕜[t]` -/

/-- **The cylinder `𝔸¹ ×_{Spec 𝕜} X` is the fibre product of `X` with the standard affine line
`Spec 𝕜[t]`, compatibly with the projections onto `X`.**

Here `𝔸¹` is `Work.CY3Stab.AffineK 1 = 𝔸(Fin 1; Spec 𝕜)`, so the left-hand scheme is the fibre
product `pullback (𝔸¹ ↘ Spec 𝕜) (X ↘ Spec 𝕜)` of `Work.CY3Stab.WProd 𝕜 X 1`.  The isomorphism is
the swap of the two legs followed by the identification `𝔸¹ ≅ Spec 𝕜[t]` of
`Work.K3Inputs.affine1_iso_specPolynomial`; the compatibility says that the projection of the
fibre product onto `X` corresponds to the projection of the cylinder onto `X`, namely the
canonical structure morphism `𝔸¹ ×_{Spec 𝕜} X ⟶ X` followed by `X ↘ Spec 𝕜` (which is what
`(WProd 𝕜 X 1 ↘ Spec 𝕜)` unfolds to, the canonical `Over X`-structure of a fibre product).

This is the shape required by `Work.K3Inputs.cylFieldAlgEquiv`. -/
theorem exists_iso_wProd_one (𝕜 : Type) [Field 𝕜] (X : Scheme.{0})
    [X.Over (Spec (CommRingCat.of 𝕜))] :
    ∃ E : pullback (Work.CY3Stab.AffineK (𝕜 := 𝕜) 1 ↘ Spec (CommRingCat.of 𝕜))
          (X ↘ Spec (CommRingCat.of 𝕜)) ≅
        pullback (X ↘ Spec (CommRingCat.of 𝕜))
          (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))),
      E.hom ≫ (pullback.fst (X ↘ Spec (CommRingCat.of 𝕜))
          (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))) ≫
          (X ↘ Spec (CommRingCat.of 𝕜))) =
        (pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) 1 ↘ Spec (CommRingCat.of 𝕜))
          (X ↘ Spec (CommRingCat.of 𝕜)) ≫ (X ↘ Spec (CommRingCat.of 𝕜))) := by
  -- `𝔸¹ = 𝔸(Fin 1; Spec 𝕜)` is the standard affine line, over the base.
  obtain ⟨τ, hτ⟩ := Work.K3Inputs.affine1_iso_specPolynomial 𝕜
  let f : Work.CY3Stab.AffineK (𝕜 := 𝕜) 1 ⟶ Spec (CommRingCat.of 𝕜) :=
    Work.CY3Stab.AffineK (𝕜 := 𝕜) 1 ↘ Spec (CommRingCat.of 𝕜)
  let g : X ⟶ Spec (CommRingCat.of 𝕜) := X ↘ Spec (CommRingCat.of 𝕜)
  let spec : Spec (CommRingCat.of (Polynomial 𝕜)) ⟶ Spec (CommRingCat.of 𝕜) :=
    Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))
  have hτ' : τ.hom ≫ spec = f := hτ
  have hτ'' : τ.inv ≫ f = spec := by
    rw [← hτ', ← Category.assoc, τ.inv_hom_id, Category.id_comp]
  -- The two legs of the fibre products are exchanged and `𝔸¹` is replaced by `Spec 𝕜[t]`.
  let e : pullback f g ⟶ pullback g spec :=
    pullback.lift (pullback.snd f g) (pullback.fst f g ≫ τ.hom)
      (by rw [Category.assoc, hτ']; exact pullback.condition.symm)
  let e' : pullback g spec ⟶ pullback f g :=
    pullback.lift (pullback.snd g spec ≫ τ.inv) (pullback.fst g spec)
      (by rw [Category.assoc, hτ'']; exact pullback.condition.symm)
  have he1 : e ≫ pullback.fst g spec = pullback.snd f g := pullback.lift_fst _ _ _
  have he2 : e ≫ pullback.snd g spec = pullback.fst f g ≫ τ.hom := pullback.lift_snd _ _ _
  have he1' : e' ≫ pullback.fst f g = pullback.snd g spec ≫ τ.inv := pullback.lift_fst _ _ _
  have he2' : e' ≫ pullback.snd f g = pullback.fst g spec := pullback.lift_snd _ _ _
  have h1 : e ≫ e' = 𝟙 (pullback f g) := by
    apply pullback.hom_ext
    · rw [Category.assoc, he1', ← Category.assoc, he2, Category.assoc, τ.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, he2', he1, Category.id_comp]
  have h2 : e' ≫ e = 𝟙 (pullback g spec) := by
    apply pullback.hom_ext
    · rw [Category.assoc, he1, he2', Category.id_comp]
    · rw [Category.assoc, he2, ← Category.assoc, he1', Category.assoc, τ.inv_hom_id,
        Category.comp_id, Category.id_comp]
  refine ⟨Iso.mk e e' h1 h2, ?_⟩
  change e ≫ (pullback.fst g spec ≫ g) = pullback.snd f g ≫ g
  rw [← Category.assoc, he1]

/-! ## 2. The residue field of the generic point of an integral `𝕜`-scheme -/

/-- **The residue field of the generic point of an integral `𝕜`-scheme is its function field**,
compatibly with the structure maps.  This is the `i = 𝟙 D` case of
`Work.CrauderKatz.residueField_genericPoint_resAlgEquiv`, stated in the form in which it composes
with `Work.K3Inputs.cylFieldAlgEquiv`. -/
theorem resAlgEquiv_genericPoint_functionField (𝕜 : Type) [Field 𝕜] {D : Scheme.{0}}
    [IrreducibleSpace D] [IsIntegral D] [D.Over (Spec (CommRingCat.of 𝕜))] :
    Work.LLink.ResAlgEquiv 𝕜 (genericPoint D) (D.functionField : Type)
      (Work.CrauderKatz.functionFieldResMap 𝕜 D) := by
  obtain ⟨E, hE⟩ := Work.CrauderKatz.residueField_genericPoint_resAlgEquiv (𝕜 := 𝕜)
    (D := D) (X := D) (𝟙 D)
  exact ⟨E, hE⟩

/-! ## 3. The residue field of the generic point of the cylinder `𝔸¹ ×_𝕜 X` -/

/-- **The residue field of the generic point of the cylinder `𝔸¹ ×_𝕜 X` of an integral `𝕜`-scheme
`X` is `κ(X)(t) = RatFunc κ(X)`**, compatibly with the structure maps `𝕜 → κ(X)(t)`.

This is the (F1)-type clause of the cylinder of `X` at exponent one: the "coordinate choice" of
the paper's stabilisation step (`cor-CYnSB`), in which the cylinder point over the base point `x`
has residue field `κ(x)(t)`.  It is the composition

`κ(𝔸¹ ×_𝕜 X) ≅ κ(X)(t)`  (function field of the cylinder, `Work.K3Inputs.cylFieldAlgEquiv`)

of the identification of the residue field of the generic point with the function field
(`resAlgEquiv_genericPoint_functionField`) applied to the model `WProd 𝕜 X 1 = 𝔸¹ ×_𝕜 X` of the
cylinder, whose fibre product shape is fixed by `exists_iso_wProd_one`. -/
theorem resAlgEquiv_genericPoint_wProd_one (𝕜 : Type) [Field 𝕜]
    (X : AlgebraicGeometry.Scheme.{0}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) X 1)] :
    Work.LLink.ResAlgEquiv 𝕜 (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X 1))
      (Work.K3Inputs.cylField 𝕜 X) (Work.K3Inputs.cylResMap 𝕜 X) := by
  -- The cylinder is the fibre product `X ×_{Spec 𝕜} Spec 𝕜[t]`.
  obtain ⟨E, hE⟩ := exists_iso_wProd_one 𝕜 X
  -- The function field of the cylinder is `κ(X)(t)`, `𝕜`-linearly.
  obtain ⟨e', he'⟩ := Work.K3Inputs.cylFieldAlgEquiv 𝕜 X (Work.CY3Stab.WProd (𝕜 := 𝕜) X 1) E hE
  -- The residue field of the generic point of the cylinder is its function field, `𝕜`-linearly.
  obtain ⟨Eres, hEres⟩ := resAlgEquiv_genericPoint_functionField (𝕜 := 𝕜)
    (D := Work.CY3Stab.WProd (𝕜 := 𝕜) X 1)
  refine ⟨Eres.trans e', ?_⟩
  rw [RingEquiv.toRingHom_trans', RingHom.comp_assoc, hEres, he']

end Work.CY3Stab.Prod
