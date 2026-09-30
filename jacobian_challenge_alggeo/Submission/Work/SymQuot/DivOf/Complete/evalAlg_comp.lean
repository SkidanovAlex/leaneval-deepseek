import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry in
/-- `Scheme.Hom.appLE` is insensitive to the proof of the inclusion and compatible with
equality of the morphism: two pullbacks of the same open along the same morphism agree. -/
lemma appLE_mor_congr {X Y : Scheme} {f f' : X ⟶ Y} (h : f = f') {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V e' := by
  subst h
  congr 1

open CategoryTheory Limits AlgebraicGeometry in
/-- **Functoriality of `Scheme.Hom.appLE` in the morphism**, global-section form.

Pulling a section of `U ⊆ Z` back along `p : Y ⟶ Z` and then along `g : X ⟶ Y` is the same as
pulling it back along the composite `g ≫ p`. -/
lemma appLE_comp_appTop {X Y Z : Scheme} (g : X ⟶ Y) (p : Y ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ p ⁻¹ᵁ U) (h' : ⊤ ≤ (g ≫ p) ⁻¹ᵁ U) :
    p.appLE U ⊤ h ≫ g.appTop = (g ≫ p).appLE U ⊤ h' := by
  have h2 : g.appLE ⊤ ⊤ (le_top : ⊤ ≤ g ⁻¹ᵁ (⊤ : Y.Opens)) = g.appTop :=
    Scheme.Hom.appLE_eq_app g
  calc p.appLE U ⊤ h ≫ g.appTop
      = p.appLE U ⊤ h ≫ g.appLE ⊤ ⊤ (le_top : ⊤ ≤ g ⁻¹ᵁ (⊤ : Y.Opens)) := by rw [h2]
    _ = (g ≫ p).appLE U ⊤ h' := by
        rw [Scheme.Hom.appLE_comp_appLE (f := g) (g := p) (U := U) (V := ⊤) (W := ⊤)
          (e₁ := h) (e₂ := (le_top : ⊤ ≤ g ⁻¹ᵁ (⊤ : Y.Opens)))]

open CategoryTheory Limits AlgebraicGeometry in
theorem evalAlg_comp {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    {V : C.left.Opens} {S S' : Type u} [CommRing S] [Algebra K S] [CommRing S'] [Algebra K S']
    (f : S →ₐ[K] S') (x : Fin n → Work.SpecLin.RPt C.toOver S)
    (h : ⊤ ≤ (Limits.Pi.lift x : Work.SpecLin.specOf (K := K) S ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n)
    (h' : ⊤ ≤ (Limits.Pi.lift (fun m => Work.SpecLin.RPt.map f (x m)) :
      Work.SpecLin.specOf (K := K) S' ⟶ Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ
      Work.SymQuot.piOpen C.toOver V n) :
    f.toRingHom.comp (evalAlg C V n x h) =
      evalAlg C V n (fun m => Work.SpecLin.RPt.map f (x m)) h' := by
  -- `Pi.lift` is natural in the source, so the point `Π_m (x m)_{S'}` is the base change of
  -- `Π_m x m` along `Spec S' ⟶ Spec S`.
  have key : (Scheme.Hom.appLE (Limits.Pi.lift x).left
        (Work.SymQuot.piOpen C.toOver V n) ⊤ h) ≫
        (Spec.map (CommRingCat.ofHom f.toRingHom)).appTop =
      Scheme.Hom.appLE (Limits.Pi.lift (fun m => Work.SpecLin.RPt.map f (x m))).left
        (Work.SymQuot.piOpen C.toOver V n) ⊤ h' := by
    have hleft : (Limits.Pi.lift (fun m => Work.SpecLin.RPt.map f (x m))).left =
        (Work.SpecLin.specOfMap (K := K) f).left ≫ (Limits.Pi.lift x).left := by
      change (Limits.Pi.lift (fun m => Work.SpecLin.specOfMap (K := K) f ≫ x m)).left =
        (Work.SpecLin.specOfMap (K := K) f).left ≫ (Limits.Pi.lift x).left
      rw [Work.SymQuot.pi_lift_comp n (Work.SpecLin.specOfMap (K := K) f) x, Over.comp_left]
    have hleft' : (Limits.Pi.lift (fun m => Work.SpecLin.RPt.map f (x m))).left =
        Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (Limits.Pi.lift x).left := hleft
    rw [appLE_mor_congr hleft' h']
    exact appLE_comp_appTop (Spec.map (CommRingCat.ofHom f.toRingHom)) (Limits.Pi.lift x).left
      (Work.SymQuot.piOpen C.toOver V n) h (hleft' ▸ h')
  -- `ΓSpecIso` is natural.
  have hnathom : (Scheme.ΓSpecIso (CommRingCat.of S')).hom.hom.comp
      (Spec.map (CommRingCat.ofHom f.toRingHom)).appTop.hom =
      f.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f.toRingHom))
  have keyhom : (Spec.map (CommRingCat.ofHom f.toRingHom)).appTop.hom.comp
      (Scheme.Hom.appLE (Limits.Pi.lift x).left (Work.SymQuot.piOpen C.toOver V n) ⊤ h).hom =
      (Scheme.Hom.appLE (Limits.Pi.lift (fun m => Work.SpecLin.RPt.map f (x m))).left
        (Work.SymQuot.piOpen C.toOver V n) ⊤ h').hom :=
    congrArg CommRingCat.Hom.hom key
  show f.toRingHom.comp ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp
      (Scheme.Hom.appLE (Limits.Pi.lift x).left (Work.SymQuot.piOpen C.toOver V n) ⊤ h).hom) =
    (Scheme.ΓSpecIso (CommRingCat.of S')).hom.hom.comp
      (Scheme.Hom.appLE (Limits.Pi.lift (fun m => Work.SpecLin.RPt.map f (x m))).left
        (Work.SymQuot.piOpen C.toOver V n) ⊤ h').hom
  rw [← RingHom.comp_assoc, ← hnathom, RingHom.comp_assoc, keyhom]

end Work.SymQuot.DivOf.Complete
