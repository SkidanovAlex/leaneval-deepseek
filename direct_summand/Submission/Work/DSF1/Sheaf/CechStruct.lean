import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Cech.CechQo

/-!
# The structure sheaf of a scheme as a presheaf of modules over its global sections

For a scheme `X`, we regard the structure sheaf `X.presheaf` as a presheaf of modules
over the ring `R = Γ(X, ⊤)` of global sections, using the restriction maps as the
structure maps.  This is the coefficient presheaf of the Čech complex discussed in
`Work.DSF1.Sheaf.structCech`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped AlgebraicGeometry Simplicial BigOperators

namespace Work.DSF1.Sheaf

universe u

/-- The structure sheaf of `X`, as a presheaf of modules over `Γ(X, ⊤)`. -/
noncomputable def structPresheaf (X : Scheme.{u}) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u} (X.presheaf.obj (op ⊤)) where
  obj U :=
    letI : Algebra ↥(X.presheaf.obj (op ⊤)) ↥(X.presheaf.obj (op U.unop)) :=
      (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom.toAlgebra
    ModuleCat.of _ ↥(X.presheaf.obj (op U.unop))
  map {U V} i :=
    letI : Algebra ↥(X.presheaf.obj (op ⊤)) ↥(X.presheaf.obj (op U.unop)) :=
      (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom.toAlgebra
    letI : Algebra ↥(X.presheaf.obj (op ⊤)) ↥(X.presheaf.obj (op V.unop)) :=
      (X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom.toAlgebra
    ModuleCat.ofHom
      { toFun := (X.presheaf.map i).hom
        map_add' := fun a b => map_add _ a b
        map_smul' := by
          intro r x
          show (X.presheaf.map i).hom
              ((X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom r * x) =
            (X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom r *
              (X.presheaf.map i).hom x
          rw [map_mul]
          congr 1
          have h : (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) ≫ (X.presheaf.map i) =
              (X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op) := by
            rw [← Functor.map_comp]
            exact congrArg (fun f => X.presheaf.map f) (Subsingleton.elim _ _)
          exact congrArg (fun f => CommRingCat.Hom.hom f r) h }
  map_id U := by first | (ext1; simp; done) | (ext1; simp; rfl)
  map_comp i j := by first | (ext1; simp; done) | (ext1; simp; rfl)

/-- The Čech complex of the structure sheaf of `X` along a family of opens, as a
complex of modules over `Γ(X, ⊤)`. -/
noncomputable abbrev structCech (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} (X.presheaf.obj (op ⊤))) ℕ :=
  (cechComplexFunctor U).obj (structPresheaf X)

/-- The family of basic opens `D (f i)` attached to a family of global sections. -/
noncomputable abbrev basicOpenFamily (X : Scheme.{u}) {ι : Type u}
    (f : ι → ↥(X.presheaf.obj (op ⊤))) : ι → X.Opens :=
  fun i => X.basicOpen (f i)

/-- The Čech complex of the structure sheaf of `X` along the family of basic opens
`D (f i)`, as a complex of modules over `Γ(X, ⊤)`. -/
noncomputable abbrev cechBasicOpen (X : Scheme.{u}) {ι : Type u}
    (f : ι → ↥(X.presheaf.obj (op ⊤))) :
    CochainComplex (ModuleCat.{u} (X.presheaf.obj (op ⊤))) ℕ :=
  structCech X (basicOpenFamily X f)

/-- The comparison map from the Čech complex of `X` along `D (f i)` to the complex
localized at `D (f i)`. -/
noncomputable abbrev locCech (X : Scheme.{u}) {ι : Type u}
    (f : ι → ↥(X.presheaf.obj (op ⊤))) (i : ι) :
    cechBasicOpen X f ⟶
      (cechComplexFunctor (basicOpenFamily X f)).obj
        (Work.DSF1.Cech.Qo (structPresheaf X) (X.basicOpen (f i))) :=
  (cechComplexFunctor (basicOpenFamily X f)).map
    (Work.DSF1.Cech.etaO (structPresheaf X) (X.basicOpen (f i)))

end Work.DSF1.Sheaf
