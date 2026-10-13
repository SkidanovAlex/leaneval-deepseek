import Mathlib
import Submission.Work.DSF1.Sheaf.restr_trans
import Submission.Work.DSF1.Sheaf.restr_refl
import Submission.Work.DSF1.Cech.CoaugCycle

/-!
# A private copy of the Čech sheaf complex used by `Work.DSEQ0.quasiIso_augZ`

The definitions `Work.DSEQ0.cechShPresheaf`, `cechSh`, `cechShZ`, `aug0`, `augN`, `augZ` live in
`Submission/Work/DSEQ0/cechModelData_exists.lean`, which is under active development by another
member of the team.  To be able to develop and delegate the proof of the theorem
`Work.DSEQ0.quasiIso_augZ` without depending on the build state of that file, the *same*
definitions are copied here, verbatim, inside the namespace `Work.DSEQ0.C`.

Each copy is definitionally equal to the original, so a proof about the copy can be transported to
a proof about the original by `rfl`/`exact` (see `Work.DSEQ0.quasiIso_augZ`).
-/

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Limits Opposite

open scoped Simplicial BigOperators

universe u

variable (X : AlgebraicGeometry.Scheme.{u})

namespace C

/-- Copy of `Work.DSEQ0.cechShPresheaf`. -/
noncomputable def cechShPresheaf : (X.Opens)ᵒᵖ ⥤ X.Modules where
  obj W := Work.DSF1.secSheaf W.unop
  map {W W'} f := Work.DSF1.Sheaf.restr (leOfHom f.unop)
  map_id W := by
    rw [show (leOfHom (𝟙 W.unop : W.unop ⟶ W.unop)) = (le_refl W.unop) from Subsingleton.elim _ _,
      Work.DSF1.Sheaf.restr_refl X W.unop]
  map_comp {W W' W''} f g := by
    rw [Work.DSF1.Sheaf.restr_trans X (leOfHom f.unop) (leOfHom g.unop)]

/-- Copy of `Work.DSEQ0.cechSh`. -/
noncomputable abbrev cechSh {ι : Type u} (U : ι → X.Opens) : CochainComplex X.Modules ℕ :=
  (cechComplexFunctor U).obj (cechShPresheaf X)

/-- Copy of `Work.DSEQ0.cechShZ`. -/
noncomputable abbrev cechShZ {ι : Type u} (U : ι → X.Opens) : CochainComplex X.Modules ℤ :=
  (cechSh X U).extend ComplexShape.embeddingUpNat

/-- Copy of `Work.DSEQ0.aug0`. -/
noncomputable def aug0 {ι : Type u} (U : ι → X.Opens) :
    (cechShPresheaf X).obj (op ⊤) ⟶ (cechSh X U).X 0 :=
  Pi.lift (fun x => (cechShPresheaf X).map (homOfLE (le_top :
    Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op)

/-- Copy of `Work.DSEQ0.augN`. -/
noncomputable def augN {ι : Type u} (U : ι → X.Opens)
    (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    (HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0).obj
        ((cechShPresheaf X).obj (op ⊤)) ⟶ cechSh X U :=
  HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℕ) (j := 0) (aug0 X U) (fun k hk => by
    have hk1 : k = 1 := by simpa using hk.symm
    subst hk1
    exact h)

/-- Copy of `Work.DSEQ0.augZ`. -/
noncomputable def augZ {ι : Type u} (U : ι → X.Opens)
    (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
        ((cechShPresheaf X).obj (op ⊤)) ⟶ cechShZ X U :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      ((cechShPresheaf X).obj (op ⊤)) 0 0 rfl).inv ≫
    HomologicalComplex.extendMap (augN X U h) ComplexShape.embeddingUpNat

end C

end Work.DSEQ0
