import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 2000000

universe u

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry

/-- Pulling back a section of an affine open `V ⊆ X` along `Spec S ⟶ Spec Γ(X,V) ⟶ X`, whose
image lies in `V`, and transporting to `S` along `ΓSpecIso`, is the same as the original ring
map `Γ(X,V) →+* S`. -/
private lemma appLE_fromSpec_comp_eq {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    {S : Type u} [CommRing S] (φ : Γ(X, V) →+* S)
    (h : (⊤ : (Spec (CommRingCat.of S)).Opens) ≤
      (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (Scheme.Hom.appLE (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) V ⊤ h) ≫
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom = CommRingCat.ofHom φ := by
  have h' : (⊤ : (Spec (CommRingCat.of S)).Opens) ≤
      (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ V) := h
  rw [Scheme.Hom.comp_appLE]
  change hV.fromSpec.app V ≫ (Spec.map (CommRingCat.ofHom φ)).appLE
      (hV.fromSpec ⁻¹ᵁ V) ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom = CommRingCat.ofHom φ
  rw [IsAffineOpen.fromSpec_app_self hV]
  simp only [Category.assoc]
  rw [Scheme.Hom.map_appLE_assoc]
  rw [show (Spec.map (CommRingCat.ofHom φ)).appLE (⊤ : (Spec Γ(X, V)).Opens) ⊤ _ =
      (Spec.map (CommRingCat.ofHom φ)).appTop from Scheme.Hom.appLE_eq_app _]
  rw [Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)]
  erw [Iso.inv_hom_id_assoc]

open CategoryTheory Limits AlgebraicGeometry in
theorem ptVal_ptOfAlgHom {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {V : C.left.Opens}
    (hV : IsAffineOpen V) {S : Type u} [CommRing S] [Algebra K S]
    (κ : Γ(C.left, V) →ₐ[K] S) (h : ⊤ ≤ (ptOfAlgHom C hV κ).left ⁻¹ᵁ V) :
    ptVal C V (ptOfAlgHom C hV κ) h = κ.toRingHom := by
  have key := appLE_fromSpec_comp_eq hV κ.toRingHom h
  change (Scheme.Hom.appLE (Spec.map (CommRingCat.ofHom κ.toRingHom) ≫ hV.fromSpec) V ⊤ h ≫
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom).hom = κ.toRingHom
  exact congrArg CommRingCat.Hom.hom key

end Work.SymQuot.DivOf.Complete
