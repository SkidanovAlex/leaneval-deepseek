/-
AREA RESOL — naturality of the augmentation `εFam` of the degreewise resolutions.

`epsFam B n : (R.obj B).X n ⟶ B.X n` is the comparison map of the resolution bicomplex of `B`
(see `RESOL/TotalRes.lean`), assembled from the degreewise augmentations `augRes (B.X p)`.  The
statement proved here is that it is natural in the complex `B`, i.e. that the components
`epsFam B n` are the components of a natural transformation `R ⟶ 𝟭 Cpx`.

The proof reduces, via the universal property of the total complex (`GradedObject.mapObj_ext`),
to the componentwise statement

`augComp B p q ≫ f.f (tshape (p,q)) = (LR.chainComplexMap (f.f p)).f q ≫ augComp B' p q`

which is the naturality of the degreewise augmentation in degree `q = 0` (the only degree in
which `augComp` is nonzero), together with the two transport lemmas
`XIsoOfEq_hom_naturality_tail` and `augRes_chainComplexMap_zero_tail` below.
-/
import Mathlib
import Submission.Work.RESOL.TotalRes
import Submission.Work.RESOL.Bicomplex

open CategoryTheory Limits LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open HomologicalComplex

noncomputable section

namespace Work.RESOL

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

attribute [local instance] Classical.propDecidable

-- the same (local) reducibility settings as in `RESOL/TotalRes.lean`, so that the definitional
-- identification of `totX B n` with `(R.obj B).X n` is available to the elaborator
set_option allowUnsafeReducibility true

attribute [local reducible] HomologicalComplex₂.total HomologicalComplex₂.toGradedObject
  HomologicalComplex₂.ιTotal HomologicalComplex₂.ιTotalOrZero GradedObject.mapObj
  GradedObject.ιMapObj GradedObject.ιMapObjOrZero bicomplexObj ComplexShape.π
  ComplexShape.ε₁ ComplexShape.ε₂ Work.RESOL.totalComplexShape

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Two transport lemmas -/

/-- The naturality of `HomologicalComplex.XIsoOfEq` with respect to a chain map, in the form in
which the transport appears in the middle of a composite (a "tail" version of
`HomologicalComplex.XIsoOfEq_hom_naturality`). -/
lemma XIsoOfEq_hom_naturality_tail {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex LightCondAb c}
    (φ : K ⟶ L) {n n' : ι} (h : n = n') {A : LightCondAb} (g : L.X n' ⟶ A) :
    φ.f n ≫ (L.XIsoOfEq h).hom ≫ g = (K.XIsoOfEq h).hom ≫ φ.f n' ≫ g := by
  rw [← Category.assoc, HomologicalComplex.XIsoOfEq_hom_naturality, Category.assoc]

/-- The naturality of the augmentation `augRes` with respect to a morphism `g`, in tail form. -/
lemma augRes_chainComplexMap_zero_tail {M N A : LightCondAb} (g : M ⟶ N) (tail : N ⟶ A) :
    (LR.chainComplexMap g).f 0 ≫ augRes N ≫ tail = augRes M ≫ g ≫ tail := by
  rw [← Category.assoc, augRes_naturality, Category.assoc]

/-! ## Naturality of the augmentation of the resolution -/

/-- **The augmentation of the resolution by atomic sums is natural in the complex.** -/
theorem epsFamNaturality {B B' : Cpx} (f : B ⟶ B') (n : ℤ) :
    CategoryTheory.CategoryStruct.comp (epsFam B n) (f.f n)
      = CategoryTheory.CategoryStruct.comp ((R.map f).f n) (epsFam B' n) := by
  -- the componentwise statement, in the total degree `tshape (p, q)`
  have core : ∀ (p : ℤ) (q : ℕ),
      augComp B p q ≫ f.f (tshape (p, q))
        = (LR.chainComplexMap (f.f p)).f q ≫ augComp B' p q := by
    intro p q
    by_cases hq : q = 0
    · -- the only nonzero case: `augComp` is the augmentation in resolution degree `0`
      simp only [augComp, dite_eq_left hq, Category.assoc]
      rw [XIsoOfEq_hom_naturality_tail (φ := LR.chainComplexMap (f.f p)) (n := q) (n' := 0) hq]
      rw [augRes_chainComplexMap_zero_tail (g := f.f p)]
      rw [← HomologicalComplex.XIsoOfEq_hom_naturality]
    · -- all other components of `augComp` vanish
      simp only [augComp, dite_eq_right hq, zero_comp, comp_zero]
  -- rewrite the statement in the total-complex form used by the lemmas of `TotalRes`
  change (CategoryTheory.CategoryStruct.comp (epsFam B n) (f.f n) : totX B n ⟶ B'.X n)
      = CategoryTheory.CategoryStruct.comp
          ((HomologicalComplex₂.total.map (bicomplexMap f) (ComplexShape.up ℤ)).f n)
          (epsFam B' n)
  apply GradedObject.mapObj_ext (X := (bicomplexObj B).toGradedObject) (p := tshape)
  intro pq hpq
  obtain ⟨p, q⟩ := pq
  -- extract the `(p, q)`-component of both sides
  rw [epsFam_comp_ιMapObj_assoc B n p q hpq]
  rw [HomologicalComplex₂.ιTotal_map_assoc (K := bicomplexObj B) (L := bicomplexObj B')
      (φ := bicomplexMap f) (c₁₂ := ComplexShape.up ℤ) p q n hpq]
  rw [epsFam_comp_ιMapObj B' n p q hpq]
  -- move the transport `(B.XIsoOfEq hpq).hom` past `f.f n` and apply the componentwise statement
  rw [Category.assoc, ← HomologicalComplex.XIsoOfEq_hom_naturality f hpq, ← Category.assoc,
    core p q, Category.assoc]
  rfl

end Work.RESOL
