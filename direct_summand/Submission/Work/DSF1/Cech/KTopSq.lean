import Mathlib
import Submission.Work.DSF1.Cech.UnitCaseSetup
import Submission.Work.DSF1.Cech.InsIdxDelta

universe u

namespace Work.DSF1.Cech

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

lemma KTopSq {X : AlgebraicGeometry.Scheme.{u}} {S : Type u} [CommRing S] {ι : Type u}
    (U : ι → X.Opens) (Q : CategoryTheory.Functor (X.Opensᵒᵖ) (ModuleCat S)) {i₀ : ι}
    (h : Work.DSF1.Cech.IsIsoDeletion U Q i₀) :
    CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CosimplicialObject.δ (Work.DSF1.Cech.Cosimplicial U Q) (1 : Fin 2))
        (Work.DSF1.Cech.k U Q h 0)
      = CategoryTheory.CategoryStruct.comp (Work.DSF1.Cech.kTop U Q h) (Work.DSF1.Cech.coaug U Q) := by
  apply Pi.hom_ext
  intro x
  conv_lhs => erw [Category.assoc, k_comp_π]
  conv_lhs => erw [← Category.assoc, cech_delta_comp_π U Q 0 (1 : Fin 2) (insIdx U i₀ 0 x)]
  conv_rhs => erw [Category.assoc]
  conv_rhs => erw [show coaug U Q ≫ Pi.π (fun z => Q.obj (op (Eobj U 0 z))) x =
      Q.map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op from Pi.lift_comp_π _ _]
  have hf1 : ((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x) = (fun _ : Fin 1 => i₀) := by
    show (CategoryTheory.Limits.FormalCoproduct.mapPower (CategoryTheory.Limits.FormalCoproduct.mk ι U)
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).f (Fin.cons i₀ x) = _
    funext a
    simp only [CategoryTheory.Limits.FormalCoproduct.mapPower, SimplexCategory.δ]
    fin_cases a
    simp
  have h0 : Eobj U 0 (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x))
      = Eobj U 0 (fun _ : Fin 1 => i₀) := congrArg (Eobj U 0) hf1
  have hδE : Q.map (homOfLE (le_top : Eobj U 0
        (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x)) ≤ ⊤)).op
      ≫ Q.map ((eqToHom h0.symm).op)
      = Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op := by
    rw [← Q.map_comp]
    congr 1
  haveI : IsIso (Q.map (homOfLE (le_top : Eobj U 0
        (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x)) ≤ ⊤)).op) := by
    rw [h0, Eobj_zero_eq U i₀]
    exact h.1
  haveI : IsIso (Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) := by
    rw [Eobj_zero_eq U i₀]
    exact h.1
  haveI : IsIso (Q.map (((E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ (insIdx U i₀ 0 x)).op) := h.2 0 x
  haveI : IsIso (coaug U Q ≫ Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (fun _ : Fin 1 => i₀)) :=
    isIso_coaug_π U Q h
  have hπ : Pi.π (fun v : Fin 1 → ι => Q.obj (op (Eobj U 0 v)))
        (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x))
      ≫ Q.map ((eqToHom h0.symm).op)
      = Pi.π (fun v : Fin 1 → ι => Q.obj (op (Eobj U 0 v))) (fun _ : Fin 1 => i₀) := by
    rw [show Q.map ((eqToHom h0.symm).op) = eqToHom (by simp only [hf1]) from by
      rw [eqToHom_op, eqToHom_map]]
    exact Pi.π_comp_eqToHom _ hf1
  have hA : Q.map (homOfLE (le_top : Eobj U 0
        (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x)) ≤ ⊤)).op
      ≫ Q.map (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).φ (insIdx U i₀ 0 x)).op
      = Q.map (homOfLE (le_top : Eobj U 1 (insIdx U i₀ 0 x) ≤ ⊤)).op := by
    rw [← Q.map_comp]
    congr 1
  have hB : Q.map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op
      ≫ Q.map (((E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ (insIdx U i₀ 0 x)).op
      = Q.map (homOfLE (le_top : Eobj U 1 (insIdx U i₀ 0 x) ≤ ⊤)).op := by
    rw [← Q.map_comp]
    congr 1
  have hγ : Q.map (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).φ (insIdx U i₀ 0 x)).op
      = inv (Q.map (homOfLE (le_top : Eobj U 0 (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x)) ≤ ⊤)).op)
        ≫ Q.map (homOfLE (le_top : Eobj U 1 (insIdx U i₀ 0 x) ≤ ⊤)).op := by
    rw [← hA, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hβ : Q.map (homOfLE (le_top : Eobj U 1 (insIdx U i₀ 0 x) ≤ ⊤)).op
      ≫ inv (Q.map (((E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ (insIdx U i₀ 0 x)).op)
      = Q.map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op := by
    rw [← hB, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hγinv : Q.map (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).φ (insIdx U i₀ 0 x)).op
      ≫ inv (Q.map (((E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ (insIdx U i₀ 0 x)).op)
      = inv (Q.map (homOfLE (le_top : Eobj U 0 (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x)) ≤ ⊤)).op)
        ≫ Q.map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op := by
    rw [hγ, Category.assoc, hβ]
  have h1 : inv (Q.map (homOfLE (le_top : Eobj U 0 (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x)) ≤ ⊤)).op)
      ≫ Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op
      = Q.map ((eqToHom h0.symm).op) := by
    rw [← hδE, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hinv : inv (Q.map (homOfLE (le_top : Eobj U 0 (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x)) ≤ ⊤)).op)
      = Q.map ((eqToHom h0.symm).op)
        ≫ inv (Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) := by
    rw [← h1, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hinvε : inv (coaug U Q ≫ Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (fun _ : Fin 1 => i₀))
      = inv (Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) := by
    have hε : coaug U Q ≫ Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (fun _ : Fin 1 => i₀)
        = Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op := Pi.lift_comp_π _ _
    have h2 : (coaug U Q ≫ Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (fun _ : Fin 1 => i₀))
        ≫ inv (Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) = 𝟙 (Q.obj (op ⊤)) := by
      rw [hε, IsIso.hom_inv_id]
    calc inv (coaug U Q ≫ Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (fun _ : Fin 1 => i₀))
        = inv (coaug U Q ≫ Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (fun _ : Fin 1 => i₀)) ≫ 𝟙 (Q.obj (op ⊤)) :=
          (Category.comp_id _).symm
      _ = inv (coaug U Q ≫ Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (fun _ : Fin 1 => i₀))
            ≫ ((coaug U Q ≫ Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (fun _ : Fin 1 => i₀))
              ≫ inv (Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op)) := by rw [h2]
      _ = (inv (coaug U Q ≫ Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (fun _ : Fin 1 => i₀))
            ≫ (coaug U Q ≫ Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (fun _ : Fin 1 => i₀)))
            ≫ inv (Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) :=
          (Category.assoc _ _ _).symm
      _ = 𝟙 (Q.obj (op (Eobj U 0 (fun _ : Fin 1 => i₀)))) ≫
            inv (Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) := by rw [IsIso.inv_hom_id]
      _ = inv (Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) := Category.id_comp _
  calc ((Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x)))
          ≫ Q.map (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).φ (insIdx U i₀ 0 x)).op)
        ≫ inv (Q.map (((E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ (insIdx U i₀ 0 x)).op)
      = Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x))
          ≫ (Q.map (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).φ (insIdx U i₀ 0 x)).op
            ≫ inv (Q.map (((E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ (insIdx U i₀ 0 x)).op)) := Category.assoc _ _ _
      _ = Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x))
          ≫ (inv (Q.map (homOfLE (le_top : Eobj U 0 (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x)) ≤ ⊤)).op)
            ≫ Q.map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op) := by rw [hγinv]
      _ = Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x))
          ≫ ((Q.map ((eqToHom h0.symm).op)
            ≫ inv (Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op))
            ≫ Q.map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op) := by rw [hinv]
      _ = ((Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (((E U).map (SimplexCategory.δ (1 : Fin 2)).op).f (insIdx U i₀ 0 x))
            ≫ Q.map ((eqToHom h0.symm).op))
            ≫ inv (Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op))
          ≫ Q.map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op := by simp only [Category.assoc]
      _ = (Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (fun _ : Fin 1 => i₀)
            ≫ inv (Q.map (homOfLE (le_top : Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op))
          ≫ Q.map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op := by
        erw [hπ]
        rfl
      _ = kTop U Q h ≫ Q.map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op := by
        erw [kTop, asIso_inv, hinvε]

end Work.DSF1.Cech
