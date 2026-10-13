import Mathlib
import Submission.Work.DSF1.Cech.CechLocalized
import Submission.Work.DSF1.Cech.CechSetup

namespace Work.DSF1.Cech

universe u
open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

variable {X : Scheme.{u}} {R : Type u} [CommRing R] {ι : Type u}

/-- The set-theoretic component of the first coface `δ 0` of the Čech nerve: inserting the
distinguished index `i` at position `0` and then deleting position `0` is the identity. -/
lemma cech_map_delta0_f (U : ι → X.Opens) (i : ι) (n : ℕ) (x : Fin (n+1) → ι) :
    ((E U).map (SimplexCategory.δ 0).op).f (insIdx U i n x) = x := by
  show (FormalCoproduct.mapPower (FormalCoproduct.mk ι U)
    (SimplexCategory.δ (0 : Fin (n+2))).toOrderHom.toFun).f (Fin.cons i x) = x
  funext a
  simp only [FormalCoproduct.mapPower]
  simp [SimplexCategory.δ, SimplexCategory.Hom.toOrderHom_mk, Fin.cons_succ]

/-- The open of the `(n+1)`-simplex obtained by inserting `i` at position `0` is the open of
the `n`-simplex intersected with `U i`. -/
lemma Eobj_insIdx (U : ι → X.Opens) (i : ι) (n : ℕ) (x : Fin (n+1) → ι) :
    Eobj U (n+1) (insIdx U i n x) = Eobj U n x ⊓ U i := by
  show (∏ᶜ (fun b : Fin (n+2) => U (insIdx U i n x b))) =
    (∏ᶜ (fun b : Fin (n+1) => U (x b))) ⊓ U i
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · exact leOfHom (Pi.lift (fun a : Fin (n+1) =>
        Pi.π (fun b : Fin (n+2) => U (insIdx U i n x b)) a.succ))
    · exact leOfHom (Pi.π (fun b : Fin (n+2) => U (insIdx U i n x b)) 0)
  · exact leOfHom (Pi.lift (Fin.cases
      (homOfLE inf_le_right)
      (fun b => homOfLE inf_le_left ≫ Pi.π (fun a : Fin (n+1) => U (x a)) b)))

/-- A map of `Qi U P i` coming from a map `f : W ⟶ V` of opens is an isomorphism as soon as
`f` becomes an equality after intersecting with `U i`. -/
lemma isIso_Qi_map (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ ModuleCat R) (i : ι)
    {V W : X.Opensᵒᵖ} (f : W ⟶ V) (h : V.unop ⊓ U i = W.unop ⊓ U i) :
    IsIso ((Qi U P i).map f) := by
  have hf : (Qi U P i).map f =
      P.map (homOfLE (inf_le_inf_right (U i) f.unop.le)).op := rfl
  rw [hf]
  have hg : IsIso (homOfLE (inf_le_inf_right (U i) f.unop.le)) :=
    homOfLE_isIso_of_eq _ h
  have hg' : IsIso ((homOfLE (inf_le_inf_right (U i) f.unop.le)).op) := (isIso_op_iff _).mpr hg
  exact @Functor.map_isIso _ _ _ _ _ _ P _ hg'

theorem isIsoDeletion_Qi {X : Scheme.{u}} {R : Type u} [CommRing R] {ι : Type u}
    (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ ModuleCat R) (i : ι) :
    Work.DSF1.Cech.IsIsoDeletion U (Work.DSF1.Cech.Qi U P i) i := by
  refine ⟨?_, ?_⟩
  · refine isIso_Qi_map U P i (homOfLE (le_top : U i ≤ ⊤)).op ?_
    show U i ⊓ U i = ⊤ ⊓ U i
    rw [inf_idem, top_inf_eq]
  · intro n x
    refine isIso_Qi_map U P i (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i n x)).op ?_
    have hf : Eobj U n (((E U).map (SimplexCategory.δ 0).op).f (insIdx U i n x)) = Eobj U n x :=
      congrArg (Eobj U n) (cech_map_delta0_f U i n x)
    have h : Eobj U (n+1) (insIdx U i n x) ⊓ U i =
        Eobj U n (((E U).map (SimplexCategory.δ 0).op).f (insIdx U i n x)) ⊓ U i := by
      rw [Eobj_insIdx U i n x, hf, inf_assoc, inf_idem]
    exact h

end Work.DSF1.Cech
