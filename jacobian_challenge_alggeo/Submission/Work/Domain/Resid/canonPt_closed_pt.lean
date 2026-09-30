import Mathlib
import Submission.Work.Domain.Resid.Setup
import Submission.Work.Domain.Resid.canonPt_closed
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Domain.Resid

theorem canonPt_closed_pt {K : Type _} [Field K] {X : Work.GCBasics.Sch K}
    [AlgebraicGeometry.IsIntegral X.left] (x : X.left)
    {A : Type _} [CommRing A] [IsLocalRing A] [Algebra K A]
    (ρ : X.left.presheaf.stalk x →+* A) [IsLocalHom ρ]
    (hKA : (Work.GCBasics.specOf K A).hom = CategoryTheory.CategoryStruct.comp
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ))
      (CategoryTheory.CategoryStruct.comp (X.left.fromSpecStalk x) X.hom)) :
    ∃ e : Work.GCBasics.resField X x →ₐ[K] IsLocalRing.ResidueField A,
      CategoryTheory.CategoryStruct.comp (Work.GCBasics.closedPt (K := K) A)
        (Work.Domain.Resid.canonPt x ρ hKA) =
        Work.GCBasics.RPt.map e (Work.GCBasics.resPt X x) := by
  haveI hloc : IsLocalHom ((IsLocalRing.residue A).comp ρ) := inferInstance
  have hklin : ∀ k : K, (Work.Domain.Resid.residueAlgHom x ρ)
      (algebraMap K (Work.GCBasics.resField X x) k) =
        algebraMap K (IsLocalRing.ResidueField A) k := by
    intro k
    let e₀ : Work.GCBasics.resField X x →+* IsLocalRing.ResidueField A :=
      Work.Domain.Resid.residueAlgHom x ρ
    have h2 : algebraMap K (Work.GCBasics.resField X x) k =
        (X.left.residue x).hom ((Spec.preimage (X.left.fromSpecStalk x ≫ X.hom)).hom k) := by
      show ((Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom)).hom) k = _
      rw [show X.left.fromSpecResidueField x =
          Spec.map (X.left.residue x) ≫ X.left.fromSpecStalk x from rfl]
      rw [Category.assoc, Spec.preimage_comp, Spec.preimage_map]
      rfl
    have he : ∀ y, e₀ ((X.left.residue x).hom y) = IsLocalRing.residue A (ρ y) :=
      fun y => RingHom.congr_fun (Work.Domain.Resid.residueAlgHom_comp x ρ) y
    have hKrho : ρ.comp (Spec.preimage (X.left.fromSpecStalk x ≫ X.hom)).hom = algebraMap K A := by
      have h := congrArg Spec.preimage hKA
      rw [Work.GCBasics.specOf_hom] at h
      simp only [Spec.preimage_comp, Spec.preimage_map] at h
      exact congrArg CommRingCat.Hom.hom h.symm
    calc e₀ (algebraMap K (Work.GCBasics.resField X x) k)
        = e₀ ((X.left.residue x).hom
            ((Spec.preimage (X.left.fromSpecStalk x ≫ X.hom)).hom k)) := congrArg e₀ h2
      _ = IsLocalRing.residue A
            (ρ ((Spec.preimage (X.left.fromSpecStalk x ≫ X.hom)).hom k)) := he _
      _ = IsLocalRing.residue A (algebraMap K A k) := by
            have h := RingHom.congr_fun hKrho k
            exact congrArg (IsLocalRing.residue A) h
      _ = algebraMap K (IsLocalRing.ResidueField A) k := rfl
  let e : Work.GCBasics.resField X x →ₐ[K] IsLocalRing.ResidueField A :=
    ⟨Work.Domain.Resid.residueAlgHom x ρ, hklin⟩
  refine ⟨e, ?_⟩
  have he : e.toRingHom.comp (X.left.residue x).hom = (IsLocalRing.residue A).comp ρ :=
    Work.Domain.Resid.residueAlgHom_comp x ρ
  have keyC : CommRingCat.ofHom ρ ≫ CommRingCat.ofHom (IsLocalRing.residue A) =
      X.left.residue x ≫ CommRingCat.ofHom e.toRingHom := by
    apply CommRingCat.hom_ext
    exact he.symm
  have hAB : Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
        Spec.map (CommRingCat.ofHom ρ) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map (X.left.residue x) :=
    (Spec.map_comp (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom (IsLocalRing.residue A))).symm.trans
      ((congrArg Spec.map keyC).trans
        (Spec.map_comp (X.left.residue x) (CommRingCat.ofHom e.toRingHom)))
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Work.GCBasics.RPt.map, Work.GCBasics.specOfMap, Over.homMk_left,
    Work.GCBasics.closedPt, Work.Domain.Resid.canonPt_left, Work.GCBasics.resPt_left,
    Scheme.fromSpecResidueField]
  rw [← Category.assoc, hAB, Category.assoc]

end Work.Domain.Resid
