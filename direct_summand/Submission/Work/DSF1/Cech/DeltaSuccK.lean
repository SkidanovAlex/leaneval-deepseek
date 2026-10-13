import Mathlib
import Submission.Work.DSF1.Cech.UnitCaseSetup
import Submission.Work.DSF1.Cech.InsIdxDelta

namespace Work.DSF1.Cech

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

universe u v

/-- Transport of a product projection along an equality of the indexing type. -/
lemma deltaSucc_pi_π_eqToHom {C : Type u} [Category C] [HasProducts C] {α : Type v} (F : α → C)
    {i j : α} (h : i = j) :
    Pi.π F i ≫ eqToHom (congrArg F h) = Pi.π F j := by
  subst h; simp

/-- The inverse of `Q.map (eqToHom e).op` is the `eqToHom` of the corresponding equality. -/
lemma deltaSucc_inv_map_eqToHom_op {C : Type u} [Category C] {D : Type v} [Category D] (Q : Cᵒᵖ ⥤ D)
    {W W' : C} (e : W = W') :
    inv (Q.map (eqToHom e).op) = eqToHom (congrArg (fun W : C => Q.obj (op W)) e) := by
  subst e; simp

/-- Naturality of inverse isomorphisms along a commutative square: if `f ≫ hh = g ≫ k` and
`Q.map f.op`, `Q.map k.op` are invertible, then `Q.map g.op ≫ inv (Q.map f.op)` equals
`inv (Q.map k.op) ≫ Q.map hh.op`. -/
lemma deltaSucc_inv_nat {C : Type u} [Category C] {D : Type v} [Category D] (Q : Cᵒᵖ ⥤ D)
    {A B Cc Dd : C} (f : A ⟶ B) (g : A ⟶ Cc) (hh : B ⟶ Dd) (k : Cc ⟶ Dd)
    (sq : f ≫ hh = g ≫ k) [IsIso (Q.map f.op)] [IsIso (Q.map k.op)] :
    Q.map g.op ≫ inv (Q.map f.op) = inv (Q.map k.op) ≫ Q.map hh.op := by
  have h1 : Q.map hh.op ≫ Q.map f.op = Q.map k.op ≫ Q.map g.op := by
    rw [← Q.map_comp, ← Q.map_comp, ← op_comp, ← op_comp, sq]
  rw [IsIso.comp_inv_eq, Category.assoc, eq_comm, IsIso.inv_comp_eq]
  exact h1

lemma DeltaSuccK {X : AlgebraicGeometry.Scheme.{u}} {S : Type u} [CommRing S] {ι : Type u}
    (U : ι → X.Opens) (Q : CategoryTheory.Functor (X.Opensᵒᵖ) (ModuleCat S)) {i₀ : ι}
    (h : Work.DSF1.Cech.IsIsoDeletion U Q i₀) (n : ℕ) (i : Fin (n+2)) :
    CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CosimplicialObject.δ (Work.DSF1.Cech.Cosimplicial U Q) i.succ)
        (Work.DSF1.Cech.k U Q h (n+1))
      = CategoryTheory.CategoryStruct.comp (Work.DSF1.Cech.k U Q h n)
        (CategoryTheory.CosimplicialObject.δ (Work.DSF1.Cech.Cosimplicial U Q) i) := by
  apply Pi.hom_ext
  intro y
  change CategoryStruct.comp
        (CategoryStruct.comp (CosimplicialObject.δ (Cosimplicial U Q) i.succ) (k U Q h (n+1)))
        (Pi.π (fun z => Q.obj (op (Eobj U (n+1) z))) y)
      = CategoryStruct.comp
        (CategoryStruct.comp (k U Q h n) (CosimplicialObject.δ (Cosimplicial U Q) i))
        (Pi.π (fun z => Q.obj (op (Eobj U (n+1) z))) y)
  conv_lhs =>
    rw [Category.assoc, k_comp_π U Q h (n+1) y, ← Category.assoc,
        cech_delta_comp_π U Q (n+1) i.succ (insIdx U i₀ (n+1) y), Category.assoc]
  conv_rhs =>
    rw [Category.assoc, cech_delta_comp_π U Q n i y, ← Category.assoc,
        k_comp_π U Q h n (((E U).map (SimplexCategory.δ i).op).f y), Category.assoc]
  have hZ : ((E U).map (SimplexCategory.δ i.succ).op).f (insIdx U i₀ (n+1) y)
      = insIdx U i₀ n (((E U).map (SimplexCategory.δ i).op).f y) := InsIdxDelta U i₀ n i y
  have hpi : Pi.π (fun z => Q.obj (op (Eobj U (n+1) z)))
        (((E U).map (SimplexCategory.δ i.succ).op).f (insIdx U i₀ (n+1) y)) ≫
      eqToHom (congrArg (fun z => Q.obj (op (Eobj U (n+1) z))) hZ) =
      Pi.π (fun z => Q.obj (op (Eobj U (n+1) z)))
        (insIdx U i₀ n (((E U).map (SimplexCategory.δ i).op).f y)) :=
    deltaSucc_pi_π_eqToHom (fun z => Q.obj (op (Eobj U (n+1) z))) hZ
  let f1 : Eobj U (n+2) (insIdx U i₀ (n+1) y) ⟶ Eobj U (n+1) y :=
    ((E U).map (SimplexCategory.δ (0 : Fin (n+3))).op).φ (insIdx U i₀ (n+1) y)
  let f2 : Eobj U (n+2) (insIdx U i₀ (n+1) y) ⟶
      Eobj U (n+1) (((E U).map (SimplexCategory.δ i.succ).op).f (insIdx U i₀ (n+1) y)) :=
    ((E U).map (SimplexCategory.δ i.succ).op).φ (insIdx U i₀ (n+1) y)
  let fi : Eobj U (n+1) y ⟶ Eobj U n (((E U).map (SimplexCategory.δ i).op).f y) :=
    ((E U).map (SimplexCategory.δ i).op).φ y
  let g0 : Eobj U (n+1) (insIdx U i₀ n (((E U).map (SimplexCategory.δ i).op).f y)) ⟶
      Eobj U n (((E U).map (SimplexCategory.δ i).op).f y) :=
    ((E U).map (SimplexCategory.δ (0 : Fin (n+2))).op).φ
      (insIdx U i₀ n (((E U).map (SimplexCategory.δ i).op).f y))
  have hsq : f1 ≫ fi = f2 ≫ (eqToHom (congrArg (Eobj U (n+1)) hZ) ≫ g0) :=
    Subsingleton.elim _ _
  haveI i1 : IsIso (Q.map f1.op) := h.2 (n+1) y
  haveI i0 : IsIso (Q.map g0.op) := h.2 n (((E U).map (SimplexCategory.δ i).op).f y)
  haveI : IsIso (Q.map (eqToHom (congrArg (Eobj U (n+1)) hZ) ≫ g0).op) := by
    rw [op_comp, Q.map_comp]; infer_instance
  have hkey := deltaSucc_inv_nat Q f1 f2 fi (eqToHom (congrArg (Eobj U (n+1)) hZ) ≫ g0) hsq
  have hkm : Q.map (eqToHom (congrArg (Eobj U (n+1)) hZ) ≫ g0).op
      = Q.map g0.op ≫ Q.map (eqToHom (congrArg (Eobj U (n+1)) hZ)).op := by
    rw [op_comp, Q.map_comp]
  have hEB : inv (Q.map (eqToHom (congrArg (Eobj U (n+1)) hZ)).op)
      = eqToHom (congrArg (fun z => Q.obj (op (Eobj U (n+1) z))) hZ) := by
    rw [deltaSucc_inv_map_eqToHom_op]
  have core : Q.map f2.op ≫ inv (Q.map f1.op)
      = eqToHom (congrArg (fun z => Q.obj (op (Eobj U (n+1) z))) hZ)
          ≫ inv (Q.map g0.op) ≫ Q.map fi.op := by
    simp only [hkey, hkm, IsIso.inv_comp, Category.assoc, hEB]
  change Pi.π (fun z => Q.obj (op (Eobj U (n+1) z)))
        (((E U).map (SimplexCategory.δ i.succ).op).f (insIdx U i₀ (n+1) y)) ≫
      (Q.map f2.op ≫ inv (Q.map f1.op)) =
    Pi.π (fun z => Q.obj (op (Eobj U (n+1) z)))
        (insIdx U i₀ n (((E U).map (SimplexCategory.δ i).op).f y)) ≫
      (inv (Q.map g0.op) ≫ Q.map fi.op)
  rw [← hpi, core, Category.assoc]

end Work.DSF1.Cech
