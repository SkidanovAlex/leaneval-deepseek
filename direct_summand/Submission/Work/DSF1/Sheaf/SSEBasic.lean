import Mathlib
import ChallengeDeps
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Cech.CechComponents
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi

/-!
# Vocabulary for the Čech descent argument (`DSF1`, lemma `sections_surjective_of_cechTriv`)

This module collects the small amount of Čech-complex bookkeeping needed by
`Work.DSF1.Sheaf.sections_surjective_of_cechTriv`:

* `resAt M h` — the restriction map `Γ(V, M) ⟶ Γ(W, M)` for `h : W ≤ V`;
* `cechN U n` — the `n`-th object of the Čech nerve of a family of opens `U`, so that the
  degree-`n` term of Mathlib's Čech complex is the product over `i : (cechN U n).I`
  of `Γ((cechN U n).obj i, M)`; note `(cechN U n).I = Fin (n+1) → ι` and
  `(cechN U n).obj i = ∏ᶜ (U ∘ i)`;
* `cech_d_eq_sum` — the differential is the alternating sum of the cofaces;
* `coface_fac` — the component of a coface;
* `d01_fac_morph` — the components of the differential `d 0 1`;
* `piLiftHom`/`piElems_π` — turning a family of elements of a product's factors into an
  element of the product, with the expected components;
* `piFin1`, `piFin2` — a `∏ᶜ` of one (resp. two) opens is the open (resp. the intersection).
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Sheaf

variable {X : Scheme.{u}} {ι : Type u}

/-- The restriction of sections `Γ(V, M) ⟶ Γ(W, M)` induced by `h : W ≤ V`. -/
noncomputable def resAt (M : SheafOfModules X.ringCatSheaf) {V W : X.Opens} (h : W ≤ V) :
    sectionsAt M V ⟶ sectionsAt M W :=
  ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map (homOfLE h).op

lemma resAt_comp (M : SheafOfModules X.ringCatSheaf) {V W Z : X.Opens} (h : W ≤ V) (h' : Z ≤ W) :
    resAt M h ≫ resAt M h' = resAt M (h'.trans h) := by
  dsimp [resAt]
  rw [← Functor.map_comp, ← op_comp]
  congr 1

lemma resAt_apply_comp (M : SheafOfModules X.ringCatSheaf) {V W Z : X.Opens} (h : W ≤ V)
    (h' : Z ≤ W) (x : ↥(sectionsAt M V)) :
    (resAt M h') ((resAt M h) x) = (resAt M (h'.trans h)) x := by
  rw [← ConcreteCategory.comp_apply, resAt_comp]

/-- The `n`-th object of the Čech nerve of the family of opens `U`. -/
noncomputable abbrev cechN (U : ι → X.Opens) (n : ℕ) : FormalCoproduct X.Opens :=
  unop ((Functor.rightOp (FormalCoproduct.mk ι U).cech).obj ⦋n⦌)

lemma cechN_I (U : ι → X.Opens) (n : ℕ) : (cechN U n).I = (Fin (n + 1) → ι) := rfl

lemma cechN_obj (U : ι → X.Opens) (n : ℕ) (i : (cechN U n).I) :
    (cechN U n).obj i = ∏ᶜ (U ∘ i) := rfl

lemma cechN_X (U : ι → X.Opens) (M : SheafOfModules X.ringCatSheaf) (n : ℕ) :
    (cechComplex U M).X n =
      ∏ᶜ (fun i : (cechN U n).I => sectionsAt M ((cechN U n).obj i)) := rfl

/-- A product of abelian groups, with a morphism from the product of the underlying types. -/
noncomputable def piLiftHom {I : Type u} (G : I → AddCommGrpCat.{u}) :
    AddCommGrpCat.of ((i : I) → ↥(G i)) ⟶ (∏ᶜ G) :=
  Pi.lift (fun i => AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun i => ↥(G i)) i))

lemma piLiftHom_π {I : Type u} (G : I → AddCommGrpCat.{u}) (i : I) :
    piLiftHom G ≫ Pi.π G i = AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun i => ↥(G i)) i) :=
  Pi.lift_comp_π _ _

lemma piElems_π {I : Type u} (G : I → AddCommGrpCat.{u}) (g : (i : I) → ↥(G i)) (i : I) :
    (Pi.π G i) ((piLiftHom G) g) = g i := by
  rw [← ConcreteCategory.comp_apply, piLiftHom_π]
  rfl

lemma piFin1 {X : Scheme.{u}} {V : X.Opens} : (∏ᶜ (fun _ : Fin 1 => V) : X.Opens) = V := by
  apply le_antisymm
  · exact (Pi.π (fun _ : Fin 1 => V) 0).down.down
  · refine (Pi.lift (fun _ : Fin 1 => homOfLE (le_refl V)) :
        V ⟶ (∏ᶜ (fun _ : Fin 1 => V) : X.Opens)).down.down

lemma piFin2 {X : Scheme.{u}} (f : Fin 2 → X.Opens) : (∏ᶜ f : X.Opens) = f 0 ⊓ f 1 := by
  apply le_antisymm
  · exact le_inf (Pi.π f 0).down.down (Pi.π f 1).down.down
  · refine (Pi.lift (fun a : Fin 2 => homOfLE ?_) : (f 0 ⊓ f 1) ⟶ (∏ᶜ f : X.Opens)).down.down
    fin_cases a
    · exact inf_le_left
    · exact inf_le_right

/-- The differential of the Čech complex is the alternating sum of the cofaces. -/
theorem cech_d_eq_sum (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    ((cechComplexFunctor U).obj P).d n (n + 1) =
      ∑ a : Fin (n + 2), (-1 : ℤ) ^ (a : ℕ) •
        (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P).δ a) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_d]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]

/-- The component of the `j`-th coface. -/
theorem coface_fac (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (j : Fin 2)
    (x : (cechN U 1).I) :
    (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P).δ j) ≫
        Pi.π (fun i : (cechN U 1).I => P.obj (op ((cechN U 1).obj i))) x
      = Pi.π (fun i : (cechN U 0).I => P.obj (op ((cechN U 0).obj i))) (x ∘ Fin.succAbove j) ≫
          P.map (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove j)).φ x).op := by
  simp only [cechN, CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor,
    Functor.whiskeringLeft_obj_obj, Functor.comp_obj, Functor.comp_map,
    Functor.rightOp_map_unop, FormalCoproduct.cech_map, FormalCoproduct.evalOp_obj_map]
  rw [Limits.Pi.lift_comp_π]
  congr 1

/-- The components of the differential `d 0 1` of the Čech complex. -/
theorem d01_fac_morph (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (x : (cechN U 1).I) :
    ((cechComplexFunctor U).obj P).d 0 1 ≫
        Pi.π (fun i : (cechN U 1).I => P.obj (op ((cechN U 1).obj i))) x
      = Pi.π (fun i : (cechN U 0).I => P.obj (op ((cechN U 0).obj i))) (x ∘ Fin.succAbove 0) ≫
          P.map (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 0)).φ x).op
        - Pi.π (fun i : (cechN U 0).I => P.obj (op ((cechN U 0).obj i))) (x ∘ Fin.succAbove 1) ≫
          P.map (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 1)).φ x).op := by
  rw [cech_d_eq_sum (U := U) (P := P) (n := 0)]
  rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_one_zsmul]
  rw [coface_fac U P 0 x, coface_fac U P 1 x]
  simp only [cechN, sub_eq_add_neg]

end Work.DSF1.Sheaf
