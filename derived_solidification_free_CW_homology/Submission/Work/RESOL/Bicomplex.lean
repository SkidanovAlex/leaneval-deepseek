/-
AREA RESOL — the resolution bicomplex of a cochain complex, its total complex, and the
comparison map to the original complex.

Given a cochain complex `B` of light condensed abelian groups, the *resolution bicomplex* has the
resolution `X.obj (B.X p)` of the `p`-th term in the `p`-th column, and its horizontal
differentials are the chain maps induced by the differentials of `B`.  Its total complex
`R.obj B` is a cochain complex of atomic sums, and the augmentation maps of the resolutions
assemble into a natural transformation `ε : R ⟶ 𝟭` which is the comparison map.

The total complex shape is `π(p,q) = p - q`, with the sign `(-1)^p` on the resolution
differentials; thus the outer differentials (those coming from `B`) are unscaled and each column
is the resolution of the corresponding term up to a global sign.
-/
import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.Resolution

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open HomologicalComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

attribute [local instance] Classical.propDecidable

instance LR_F_preservesZeroMorphisms : LR.F.PreservesZeroMorphisms := cov_preservesZeroMorphisms

/-! ## The total complex shape -/

/-- The total complex shape for the resolution bicomplex: the first index is the degree in `B`,
the second the resolution degree. -/
instance totalComplexShape :
    TotalComplexShape (ComplexShape.up ℤ) (ComplexShape.down ℕ) (ComplexShape.up ℤ) where
  π := fun pq => pq.1 - (pq.2 : ℤ)
  ε₁ := fun _ => 1
  ε₂ := fun pq => Int.negOnePow pq.1
  rel₁ := by
    rintro p p' h q
    simp only [ComplexShape.up_Rel] at h
    simp only [ComplexShape.up_Rel]
    omega
  rel₂ := by
    rintro p q q' h
    simp only [ComplexShape.down_Rel] at h
    simp only [ComplexShape.up_Rel]
    omega
  ε₂_ε₁ := by
    rintro p p' q q' h₁ h₂
    simp only [ComplexShape.up_Rel] at h₁
    subst h₁
    simp [Int.negOnePow_succ]

/-! ## The resolution bicomplex -/

/-- The category of bicomplexes used for the resolution. -/
abbrev Bicomplex : Type 1 := HomologicalComplex₂ LightCondAb (ComplexShape.up ℤ)
  (ComplexShape.down ℕ)

/-- The resolution bicomplex of a cochain complex. -/
noncomputable def bicomplexObj (B : Cpx) : Bicomplex where
  X p := LR.chainComplex (B.X p)
  d p p' := LR.chainComplexMap (B.d p p')
  shape := by
    intro p p' h
    rw [HomologicalComplex.shape B p p' h, LR.chainComplexMap_zero]
  d_comp_d' := by
    intro p p' p'' h₁ h₂
    rw [← LR.chainComplexMap_comp]
    have h : B.d p p' ≫ B.d p' p'' = 0 := HomologicalComplex.d_comp_d B p p' p''
    rw [h, LR.chainComplexMap_zero]

/-- The map of resolution bicomplexes induced by a morphism of cochain complexes. -/
noncomputable def bicomplexMap {B B' : Cpx} (f : B ⟶ B') :
    bicomplexObj B ⟶ bicomplexObj B' where
  f p := LR.chainComplexMap (f.f p)
  comm' := by
    intro p p' h
    show LR.chainComplexMap (f.f p) ≫ LR.chainComplexMap (B'.d p p') =
      LR.chainComplexMap (B.d p p') ≫ LR.chainComplexMap (f.f p')
    rw [← LR.chainComplexMap_comp, ← LR.chainComplexMap_comp, HomologicalComplex.Hom.comm]

/-- The functor sending a cochain complex to its resolution bicomplex. -/
noncomputable def bicomplexFunctor : Cpx ⥤ Bicomplex where
  obj := bicomplexObj
  map f := bicomplexMap f
  map_id B := by
    apply HomologicalComplex.hom_ext
    intro p
    dsimp only [bicomplexMap]
    rw [HomologicalComplex.id_f, LR.chainComplexMap_id, HomologicalComplex.id_f]
    rfl
  map_comp {B B' B''} f g := by
    apply HomologicalComplex.hom_ext
    intro p
    rw [HomologicalComplex.comp_f (bicomplexMap f) (bicomplexMap g) p]
    dsimp only [bicomplexMap]
    rw [HomologicalComplex.comp_f, LR.chainComplexMap_comp]

/-- The map of resolution bicomplexes induced by the identity is the identity. -/
theorem bicomplexMap_id (B : Cpx) : bicomplexMap (𝟙 B) = 𝟙 (bicomplexObj B) :=
  bicomplexFunctor.map_id B

/-- The map of resolution bicomplexes is compatible with composition. -/
theorem bicomplexMap_comp {B C D : Cpx} (f : B ⟶ C) (g : C ⟶ D) :
    bicomplexMap (f ≫ g) = bicomplexMap f ≫ bicomplexMap g :=
  bicomplexFunctor.map_comp f g

/-- The total complex of the resolution bicomplex: the resolution of a complex by atomic sums. -/
noncomputable def R : Cpx ⥤ Cpx :=
  bicomplexFunctor ⋙ HomologicalComplex₂.totalFunctor LightCondAb (ComplexShape.up ℤ)
    (ComplexShape.down ℕ) (ComplexShape.up ℤ)

end Work.RESOL
