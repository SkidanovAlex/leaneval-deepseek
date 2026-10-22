import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.Toolkit.EA
import Submission.Work.ATOM.ZS.Topo.Defs
import Submission.Work.ATOM.zfreeTensorIso_natural

namespace Work.ATOM.Toolkit

open CategoryTheory MonoidalCategory LightCondensed LightProfinite Limits

noncomputable section

/-! ## Two auxiliary categorical lemmas

The descent statement below is a special case of the fact that *the tensor product of light
condensed abelian groups is right exact*: for a fixed `B`, the endofunctor `- ⊗ B` sends the
cokernel projection of `f : X ⟶ Y` to the cokernel projection of `f ▷ B`.

`Work.ATOM.PS_whiskerRight_cokernel_desc` records this in the form needed here (and it is
independent of `P`, so it can be reused elsewhere, e.g. for `Work.ATOM.EApp`).  It is proved by
moving the cokernel to the *second* factor of the tensor product with the braiding (where it can be
curried out, using that `- ⊗ B` is a left adjoint) and then transferring the resulting universal
property back across the braiding.

The statements are kept free of the `P`-notation so that no rewriting ever has to unfold the
definition of `Work.ATOM.P`; the specialisation to `f = P_map` is `Work.ATOM.PS_descent`. -/

/-- Currying a zero morphism in the second variable gives zero. -/
lemma PS_curry_zero (B Y X : LightCondAb) :
    MonoidalClosed.curry (0 : B ⊗ Y ⟶ X) = 0 := by
  rw [MonoidalClosed.curry_eq]
  simp

/-- **The tensor product is right exact in the second variable.**  For a morphism
`f : X ⟶ Y` and a morphism `φ : Y ⊗ B ⟶ M` killing the image of `f ▷ B`, there is a unique
morphism `ψ : cokernel f ⊗ B ⟶ M` with `(cokernel.π f ▷ B) ≫ ψ = φ`.  Equivalently:
`cokernel.π f ▷ B` is a cokernel of `f ▷ B`. -/
theorem PS_whiskerRight_cokernel_desc (B : LightCondAb) {X Y : LightCondAb} (f : X ⟶ Y)
    {M : LightCondAb} (φ : Y ⊗ B ⟶ M) (h : (f ▷ B) ≫ φ = 0) :
    ∃! ψ : cokernel f ⊗ B ⟶ M, (cokernel.π f ▷ B) ≫ ψ = φ := by
  -- Transport the cokernel to the second factor, where `curry` applies.
  have hβ : (β_ X B).inv ≫ (f ▷ B) ≫ (β_ Y B).hom = B ◁ f := by
    rw [BraidedCategory.braiding_naturality_left f B, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  have hχ : (B ◁ f) ≫ ((β_ Y B).inv ≫ φ) = 0 := by
    rw [← hβ]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, h, comp_zero]
  -- Curry and use the universal property of `cokernel f` in `LightCondAb`.
  have hg : f ≫ MonoidalClosed.curry ((β_ Y B).inv ≫ φ) = 0 := by
    rw [← MonoidalClosed.curry_natural_left f ((β_ Y B).inv ≫ φ), hχ, PS_curry_zero]
  have hd : cokernel.π f ≫ cokernel.desc f (MonoidalClosed.curry ((β_ Y B).inv ≫ φ)) hg
      = MonoidalClosed.curry ((β_ Y B).inv ≫ φ) := cokernel.π_desc _ _ _
  refine ⟨(β_ (cokernel f) B).hom ≫ MonoidalClosed.uncurry
      (cokernel.desc f (MonoidalClosed.curry ((β_ Y B).inv ≫ φ)) hg), ?_, ?_⟩
  · show (cokernel.π f ▷ B) ≫ ((β_ (cokernel f) B).hom ≫ MonoidalClosed.uncurry
      (cokernel.desc f (MonoidalClosed.curry ((β_ Y B).inv ≫ φ)) hg)) = φ
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left (cokernel.π f) B,
      Category.assoc, ← MonoidalClosed.uncurry_natural_left (cokernel.π f)
        (cokernel.desc f (MonoidalClosed.curry ((β_ Y B).inv ≫ φ)) hg), hd,
      MonoidalClosed.uncurry_curry, Iso.hom_inv_id_assoc]
  · intro χ' hχ'
    have hβ' : (β_ Y B).inv ≫ (cokernel.π f ▷ B) ≫ (β_ (cokernel f) B).hom = B ◁ cokernel.π f := by
      rw [BraidedCategory.braiding_naturality_left (cokernel.π f) B, ← Category.assoc,
        Iso.inv_hom_id, Category.id_comp]
    have hstep : (B ◁ cokernel.π f) ≫ (β_ (cokernel f) B).inv ≫ χ' = (β_ Y B).inv ≫ φ := by
      rw [← hβ']
      simp only [Category.assoc, Iso.hom_inv_id_assoc, hχ']
    have hd' : MonoidalClosed.curry ((β_ (cokernel f) B).inv ≫ χ')
        = cokernel.desc f (MonoidalClosed.curry ((β_ Y B).inv ≫ φ)) hg := by
      apply (cancel_epi (cokernel.π f)).mp
      rw [hd]
      apply MonoidalClosed.uncurry_injective
      rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
        MonoidalClosed.uncurry_curry]
      exact hstep
    have h2 : (β_ (cokernel f) B).inv ≫ χ' = MonoidalClosed.uncurry
        (cokernel.desc f (MonoidalClosed.curry ((β_ Y B).inv ≫ φ)) hg) := by
      rw [← MonoidalClosed.uncurry_curry ((β_ (cokernel f) B).inv ≫ χ'), hd']
    rw [← h2, Iso.hom_inv_id_assoc]

/-- `Work.ATOM.PS_whiskerRight_cokernel_desc` for `f = P_map = zmap ι`, rewritten in the
notation of the `ATOM` area (`P`, `P_proj`).  All the objects in the statement are `P`-notation,
so that no later rewriting has to unfold `Work.ATOM.P`. -/
theorem PS_descent (S : LightProfinite.{0}) {M : LightCondAb}
    (φ' : tmul (zfree (ℕ∪{∞})) (zfree S) ⟶ M)
    (h : (P_map ▷ zfree S) ≫ φ' = 0) :
    ∃! ψ : tmul P (zfree S) ⟶ M, (P_proj ▷ zfree S) ≫ ψ = φ' := by
  obtain ⟨ψ, hψ, huniq⟩ := PS_whiskerRight_cokernel_desc (zfree S) P_map φ' h
  exact ⟨ψ, hψ, fun y hy => huniq y hy⟩

/-- **Descent along `ℤ[(ℕ∪{∞}) ⊗ S] ⟶ P ⊗ ℤ[S]`.**  A morphism out of `ℤ[(ℕ∪{∞}) ⊗ S]` which
kills the image of `ℤ[{∞} ⊗ S]` (i.e. the composite `zmap (whiskerRight ι S)`) descends uniquely
along `Work.ATOM.EA S`.  Route: `EA S` is `(zfreeTensorIso _ _).inv ≫ (P_proj ▷ ℤ[S])`; `P_proj` is
the cokernel projection of `P_map = zmap ι`, and `- ▷ ℤ[S]` preserves cokernels
(`PreservesCokernel.iso`, `PreservesCokernel.π_iso_hom` of Mathlib's
`CategoryTheory.Limits.Preserves.Shapes.Kernels`, applied to `MonoidalCategory.tensorRight`); the
hypothesis is transported across `Work.ATOM.zfreeTensorIso_natural`. -/
theorem PS_desc (S : LightProfinite.{0}) {M : LightCondAb}
    (φ : Work.ATOM.zfree (Work.ATOM.NS S) ⟶ M)
    (hφ : Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι S) ≫ φ = 0) :
    ∃! ψ : Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S) ⟶ M,
      Work.ATOM.EA S ≫ ψ = φ := by
  -- The hypothesis, transported along `zfreeTensorIso` to `ℤ[ℕ∪{∞}] ⊗ ℤ[S]`.
  have hnat : whiskerRight P_map (zfree S) ≫ (zfreeTensorIso (ℕ∪{∞}) S).hom
      = (zfreeTensorIso pt S).hom ≫ zmap (whiskerRight LightCondensed.ι S) := by
    have h := zfreeTensorIso_natural (X := pt) (X' := ℕ∪{∞}) (Y := S) (Y' := S)
      LightCondensed.ι (𝟙 S)
    simpa [P_map, zmap, Functor.comp_map, MonoidalCategory.whiskerLeft_id, Category.comp_id,
      Category.id_comp] using h
  have hφ' : (P_map ▷ zfree S) ≫ ((zfreeTensorIso (ℕ∪{∞}) S).hom ≫ φ) = 0 := by
    rw [← Category.assoc, hnat, Category.assoc, hφ, comp_zero]
  -- Descent along the cokernel projection `P_proj ▷ ℤ[S]`.
  obtain ⟨ψ, hψ, huniq⟩ := PS_descent S ((zfreeTensorIso (ℕ∪{∞}) S).hom ≫ φ) hφ'
  have hEA : EA S = (zfreeTensorIso (ℕ∪{∞}) S).inv ≫ (P_proj ▷ zfree S) := rfl
  have hEA2 : (zfreeTensorIso (ℕ∪{∞}) S).hom ≫ EA S = P_proj ▷ zfree S := by
    rw [hEA, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  refine ⟨ψ, ?_, ?_⟩
  · -- `EA S ≫ ψ = φ`, using that `EA S` is `(zfreeTensorIso _ _).inv ≫ (P_proj ▷ ℤ[S])`.
    calc EA S ≫ ψ
        = ((zfreeTensorIso (ℕ∪{∞}) S).inv ≫ (P_proj ▷ zfree S)) ≫ ψ := rfl
      _ = (zfreeTensorIso (ℕ∪{∞}) S).inv ≫ ((P_proj ▷ zfree S) ≫ ψ) := Category.assoc _ _ _
      _ = (zfreeTensorIso (ℕ∪{∞}) S).inv ≫ ((zfreeTensorIso (ℕ∪{∞}) S).hom ≫ φ) := by rw [hψ]
      _ = φ := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · -- Uniqueness: any other `χ` with `EA S ≫ χ = φ` also satisfies the equation defining `ψ`.
    intro χ hχ
    have h3 : (P_proj ▷ zfree S) ≫ χ = (zfreeTensorIso (ℕ∪{∞}) S).hom ≫ φ := by
      calc (P_proj ▷ zfree S) ≫ χ
          = ((zfreeTensorIso (ℕ∪{∞}) S).hom ≫ EA S) ≫ χ := by rw [hEA2]
          _ = (zfreeTensorIso (ℕ∪{∞}) S).hom ≫ (EA S ≫ χ) := Category.assoc _ _ _
          _ = (zfreeTensorIso (ℕ∪{∞}) S).hom ≫ φ := by rw [hχ]
    exact huniq χ h3

end

end Work.ATOM.Toolkit
