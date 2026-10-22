import Submission.Work.ATOM.Defs

/-!
# AREA ATOM — transferring between `Hom_D` and `Hom_K` along `DerivedCategory.Qh`

Mathlib's `DerivedCategory.Q` is `HomotopyCategory.quotient ⋙ Qh` only up to the natural
isomorphism `DerivedCategory.quotientCompQhIso`.  This file records the resulting transport
lemma `Work.ATOM.bijective_pre_map_qci`, used to compare precomposition by a morphism in
`D(LightCondAb)` with precomposition by its image under `Qh`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ATOM

/-- The bijection `Hom(Qh(hq X), Qh(hq Z)) ≃ Hom(Q X, Q Z)` induced by
`DerivedCategory.quotientCompQhIso`. -/
def qciHomEquiv (X Z : CochainComplex LightCondAb ℤ) :
    (DerivedCategory.Qh.obj (hq.obj X) ⟶ DerivedCategory.Qh.obj (hq.obj Z)) ≃
      (DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Z) where
  toFun ψ := (DerivedCategory.quotientCompQhIso LightCondAb).inv.app X ≫ ψ ≫
    (DerivedCategory.quotientCompQhIso LightCondAb).hom.app Z
  invFun φ := (DerivedCategory.quotientCompQhIso LightCondAb).hom.app X ≫ φ ≫
    (DerivedCategory.quotientCompQhIso LightCondAb).inv.app Z
  left_inv ψ := by
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    simp
  right_inv φ := by
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    simp

/-- The key compatibility: `qciHomEquiv` intertwines precomposition with `Qh (hq f)` and
precomposition with `Q f`. -/
lemma qciHomEquiv_natural (X Y Z : CochainComplex LightCondAb ℤ) (f : X ⟶ Y)
    (ψ : DerivedCategory.Qh.obj (hq.obj Y) ⟶ DerivedCategory.Qh.obj (hq.obj Z)) :
    qciHomEquiv X Z (DerivedCategory.Qh.map (hq.map f) ≫ ψ) =
      DerivedCategory.Q.map f ≫ qciHomEquiv Y Z ψ := by
  simp only [qciHomEquiv, Equiv.coe_fn_mk]
  rw [← Category.assoc (DerivedCategory.Q.map f),
    DerivedCategory.quotientCompQhIso_inv_naturality f]
  simp only [Category.assoc]

/-- Transport of the bijectivity of a precomposition map from `D(LightCondAb)` to the
homotopy category: if precomposition with `Q f` is bijective on `Hom_D(Q Y, Q Z)`, then
precomposition with `Qh (hq f)` is bijective on `Hom_K(hq Y, Qh(hq Z))`. -/
theorem bijective_pre_map_qci {X Y Z : CochainComplex LightCondAb ℤ} (f : X ⟶ Y)
    (h : Function.Bijective (fun ψ : DerivedCategory.Q.obj Y ⟶ DerivedCategory.Q.obj Z =>
      DerivedCategory.Q.map f ≫ ψ)) :
    Function.Bijective (fun ψ : DerivedCategory.Qh.obj (hq.obj Y) ⟶
      DerivedCategory.Qh.obj (hq.obj Z) => DerivedCategory.Qh.map (hq.map f) ≫ ψ) := by
  have h' : Function.Bijective (fun ψ : DerivedCategory.Qh.obj (hq.obj Y) ⟶
      DerivedCategory.Qh.obj (hq.obj Z) =>
        DerivedCategory.Q.map f ≫ qciHomEquiv Y Z ψ) := by
    have heq : (fun ψ : DerivedCategory.Qh.obj (hq.obj Y) ⟶ DerivedCategory.Qh.obj (hq.obj Z) =>
        DerivedCategory.Q.map f ≫ qciHomEquiv Y Z ψ) =
        (fun φ : DerivedCategory.Q.obj Y ⟶ DerivedCategory.Q.obj Z =>
          DerivedCategory.Q.map f ≫ φ) ∘ ⇑(qciHomEquiv Y Z) := by
      funext ψ
      rfl
    rw [heq]
    exact Function.Bijective.comp h (qciHomEquiv Y Z).bijective
  have h'' : Function.Bijective ((⇑(qciHomEquiv X Z)) ∘
      (fun ψ : DerivedCategory.Qh.obj (hq.obj Y) ⟶ DerivedCategory.Qh.obj (hq.obj Z) =>
        DerivedCategory.Qh.map (hq.map f) ≫ ψ)) := by
    have heq : ((⇑(qciHomEquiv X Z)) ∘
        (fun ψ : DerivedCategory.Qh.obj (hq.obj Y) ⟶ DerivedCategory.Qh.obj (hq.obj Z) =>
          DerivedCategory.Qh.map (hq.map f) ≫ ψ)) =
        (fun ψ : DerivedCategory.Qh.obj (hq.obj Y) ⟶ DerivedCategory.Qh.obj (hq.obj Z) =>
          DerivedCategory.Q.map f ≫ qciHomEquiv Y Z ψ) := by
      funext ψ
      simpa using (qciHomEquiv_natural X Y Z f ψ)
    rw [heq]
    exact h'
  exact (Function.Bijective.of_comp_iff' (qciHomEquiv X Z).bijective _).mp h''

end Work.ATOM
