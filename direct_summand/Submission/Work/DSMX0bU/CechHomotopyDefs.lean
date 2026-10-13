import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Cech.DeltaSuccK

/-!
# The contracting homotopy of the Čech complex of a family containing a cover of `V`

Definitions and easy component identities for the contracting homotopy `cechK` of the Čech
complex of a family `i ↦ V ⊓ U i` with `V ≤ U i₀` (coefficients in a presheaf of abelian
groups).  The main use is in `Submission.Work.DSMX0bU.cechTrivAll_of_le_mem`.

Since `V ⊓ U i ≤ V = V ⊓ U i₀`, the insertion of the index `i₀` at position `0` does not
change the intersections of the family, and the coface maps of the Čech complex that it
induces are isomorphisms; this gives a contracting homotopy of the complex.
-/

namespace Work.DSMX0bU

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}

/-! ## The geometry: inserting the index `i₀` does not change the intersections -/

/-- The open `Eobj (fun i => V ⊓ U i) (n+1) (insIdx ... i₀ n x)` — the intersection of the
`V ⊓ U (x a)` together with `V ⊓ U i₀` — is equal to `Eobj (fun i => V ⊓ U i) n x`, because
every `V ⊓ U (x a)` is contained in `V` and `V ⊓ U i₀ = V`. -/
lemma Eobj_insIdx_eq (U : ι → X.Opens) (i₀ : ι) (V : X.Opens) (hV : V ≤ U i₀)
    (n : ℕ) (x : (Work.DSF1.Cech.E (fun i => V ⊓ U i)).obj (op ⦋n⦌) |>.I) :
    Work.DSF1.Cech.Eobj (fun i => V ⊓ U i) (n + 1)
        (Work.DSF1.Cech.insIdx (fun i => V ⊓ U i) i₀ n x) =
      Work.DSF1.Cech.Eobj (fun i => V ⊓ U i) n x := by
  show (∏ᶜ ((fun i => V ⊓ U i) ∘ Fin.cons i₀ x)) = ∏ᶜ ((fun i => V ⊓ U i) ∘ x)
  apply le_antisymm
  · exact leOfHom (Pi.lift (fun b => Pi.π _ b.succ))
  · exact leOfHom (Pi.lift (fun a => Fin.cases
      (Pi.π _ (0 : Fin (n+1)) ≫ homOfLE (le_inf inf_le_left (le_trans inf_le_left hV)))
      (fun b => Pi.π _ b) a))

/-- The coface maps of the Čech complex which insert `i₀` are isomorphisms: they are morphisms
between equal opens, and morphisms of a poset between equal objects are isomorphisms. -/
lemma isIso_cof0 (U : ι → X.Opens) (i₀ : ι) (V : X.Opens) (hV : V ≤ U i₀)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (x : (Work.DSF1.Cech.E (fun i => V ⊓ U i)).obj (op ⦋n⦌) |>.I) :
    IsIso (P.map (((Work.DSF1.Cech.E (fun i => V ⊓ U i)).map (SimplexCategory.δ 0).op).φ
      (Work.DSF1.Cech.insIdx (fun i => V ⊓ U i) i₀ n x)).op) := by
  have hφ : ((Work.DSF1.Cech.E (fun i => V ⊓ U i)).map (SimplexCategory.δ 0).op).φ
      (Work.DSF1.Cech.insIdx (fun i => V ⊓ U i) i₀ n x) =
      eqToHom (Eobj_insIdx_eq U i₀ V hV n x) := Subsingleton.elim _ _
  rw [hφ]
  infer_instance

/-! ## The contracting homotopy -/

/-- The cosimplicial object (in abelian groups) whose alternating coface complex is the Čech
complex of the family `i ↦ V ⊓ U i` with coefficients in `P`. -/
noncomputable abbrev Cosi (U : ι → X.Opens) (V : X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) : CosimplicialObject (AddCommGrpCat.{u}) :=
  (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι (fun i => V ⊓ U i)).cech).obj P

/-- The coface `δ i` of the Čech cosimplicial object, viewed as a map of the Čech cochain
complex. -/
noncomputable abbrev cechDelta (U : ι → X.Opens) (V : X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (i : Fin (n+2)) :
    ((cechComplexFunctor (fun i => V ⊓ U i)).obj P).X n ⟶
      ((cechComplexFunctor (fun i => V ⊓ U i)).obj P).X (n+1) :=
  (Cosi U V P).δ i

/-- The `y`-th component of the coface `δ i` of the Čech cosimplicial object. -/
lemma cech_delta_comp_π (U : ι → X.Opens) (V : X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (i : Fin (n+2))
    (y : (Work.DSF1.Cech.E (fun i => V ⊓ U i)).obj (op ⦋n+1⦌) |>.I) :
    (Cosi U V P).δ i ≫
        Pi.π (fun y => P.obj (op (Work.DSF1.Cech.Eobj (fun i => V ⊓ U i) (n+1) y))) y =
      Pi.π (fun z => P.obj (op (Work.DSF1.Cech.Eobj (fun i => V ⊓ U i) n z)))
          (((Work.DSF1.Cech.E (fun i => V ⊓ U i)).map (SimplexCategory.δ i).op).f y) ≫
        P.map (((Work.DSF1.Cech.E (fun i => V ⊓ U i)).map (SimplexCategory.δ i).op).φ y).op := by
  show Pi.lift _ ≫ Pi.π _ y = _
  exact Pi.lift_comp_π _ _

/-- The contracting homotopy of the Čech complex in degree `n`: it projects to the index
obtained by inserting `i₀` and then applies the inverse of the (iso) coface map. -/
noncomputable def cechK (U : ι → X.Opens) (i₀ : ι) (V : X.Opens) (hV : V ≤ U i₀)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    ((cechComplexFunctor (fun i => V ⊓ U i)).obj P).X (n+1) ⟶
    ((cechComplexFunctor (fun i => V ⊓ U i)).obj P).X n :=
  Pi.lift (fun x => Pi.π (fun y => P.obj (op (Work.DSF1.Cech.Eobj (fun i => V ⊓ U i) (n+1) y)))
      (Work.DSF1.Cech.insIdx (fun i => V ⊓ U i) i₀ n x) ≫
    @inv _ _ _ _ (P.map (((Work.DSF1.Cech.E (fun i => V ⊓ U i)).map (SimplexCategory.δ 0).op).φ
      (Work.DSF1.Cech.insIdx (fun i => V ⊓ U i) i₀ n x)).op) (isIso_cof0 U i₀ V hV P n x))

/-- The `x`-th component of the homotopy `cechK n`. -/
lemma cechK_comp_π (U : ι → X.Opens) (i₀ : ι) (V : X.Opens) (hV : V ≤ U i₀)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (x : (Work.DSF1.Cech.E (fun i => V ⊓ U i)).obj (op ⦋n⦌) |>.I) :
    cechK U i₀ V hV P n ≫
        Pi.π (fun z => P.obj (op (Work.DSF1.Cech.Eobj (fun i => V ⊓ U i) n z))) x =
      Pi.π (fun y => P.obj (op (Work.DSF1.Cech.Eobj (fun i => V ⊓ U i) (n+1) y)))
        (Work.DSF1.Cech.insIdx (fun i => V ⊓ U i) i₀ n x) ≫
        @inv _ _ _ _ (P.map (((Work.DSF1.Cech.E (fun i => V ⊓ U i)).map (SimplexCategory.δ 0).op).φ
          (Work.DSF1.Cech.insIdx (fun i => V ⊓ U i) i₀ n x)).op) (isIso_cof0 U i₀ V hV P n x) := by
  rw [cechK]
  exact Pi.lift_comp_π _ _

/-- The "extra codegeneracy" identity `δ₀ ≫ cechK = 𝟙` in degree `n`. -/
lemma delta0_comp_cechK (U : ι → X.Opens) (i₀ : ι) (V : X.Opens) (hV : V ≤ U i₀)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    cechDelta U V P n (0 : Fin (n+2)) ≫ cechK U i₀ V hV P n = 𝟙 _ := by
  apply Pi.hom_ext
  intro x
  show ((Cosi U V P).δ (0 : Fin (n+2)) ≫ cechK U i₀ V hV P n) ≫
      Pi.π (f := fun z => P.obj (op (Work.DSF1.Cech.Eobj (fun i => V ⊓ U i) n z))) x =
    Pi.π (f := fun z => P.obj (op (Work.DSF1.Cech.Eobj (fun i => V ⊓ U i) n z))) x
  rw [Category.assoc, cechK_comp_π, ← Category.assoc, cech_delta_comp_π]
  rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

end Work.DSMX0bU
