import Mathlib
import Submission.Work.AbVar.SmoothReduced.isGeometricallyReduced_of_smooth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A smooth morphism of schemes is geometrically reduced

We prove that a smooth morphism `f : X ⟶ S` of schemes is geometrically reduced, i.e. that
for every field `K` and every morphism `Spec K ⟶ S` the base change `X ×_S Spec K` is reduced.

The mathematical input is the classical theorem that a smooth algebra over a field is reduced
(`Work.AbVar.SmoothReduced.isReduced_of_smooth_of_field`, proved in
`Submission.Work.AbVar.SmoothReduced.isGeometricallyReduced_of_smooth`).  Smoothness is stable
under base change, so it remains to show that a scheme `Z` which is smooth over the spectrum of
a field `K` is reduced; this is checked on an affine open cover of `Z`, where the structure map
becomes a smooth ring homomorphism `K → Γ(Z, U)`.
-/
namespace Work.AbVar.SmoothReduced

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

universe u

/-- A scheme smooth over the spectrum of a field is reduced. -/
lemma isReduced_of_smoothOverSpecField {K : Type u} [Field K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (CommRingCat.of K)) [Smooth g] : IsReduced Z := by
  haveI : MorphismProperty.RespectsLeft @Smooth @IsOpenImmersion :=
    (inferInstance : MorphismProperty.Respects @Smooth @IsOpenImmersion).toRespectsLeft
  refine @IsReduced.of_openCover Z Z.affineCover ?_
  intro i
  -- the restriction of `g` to the affine chart `Spec Γ(Z, Uᵢ)` is smooth
  have hsm : Smooth (Z.affineCover.f i ≫ g) :=
    MorphismProperty.RespectsLeft.precomp (Z.affineCover.f i) (Z.affineCover.map_prop i) g
      ‹Smooth g›
  haveI : IsAffine (Z.affineCover.X i) := inferInstance
  haveI : IsAffine (Spec (CommRingCat.of K)) := inferInstance
  -- hence `K → Γ(Z, Uᵢ)` is a smooth ring homomorphism
  have hφ : RingHom.Smooth (((Z.affineCover.f i ≫ g).appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _))
      (HasRingHomProperty.appTop @Smooth (Z.affineCover.f i ≫ g) hsm)
  haveI : IsReduced Γ(Z.affineCover.X i, ⊤) := by
    letI : Algebra K Γ(Z.affineCover.X i, ⊤) :=
      (((Z.affineCover.f i ≫ g).appTop).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    haveI : Algebra.Smooth K Γ(Z.affineCover.X i, ⊤) := (RingHom.smooth_algebraMap).mp hφ
    exact isReduced_of_smooth_of_field K Γ(Z.affineCover.X i, ⊤)
  exact isReduced_of_isAffine_isReduced _

/-- **A smooth morphism of schemes is geometrically reduced.** -/
theorem geometricallyReduced_of_smooth {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] : AlgebraicGeometry.GeometricallyReduced f := by
  refine ⟨fun {K} _ y {Z} fst snd h => ?_⟩
  haveI : Smooth snd := MorphismProperty.of_isPullback h ‹Smooth f›
  exact isReduced_of_smoothOverSpecField snd

end

end Work.AbVar.SmoothReduced
