import Mathlib
import Submission.Work.Domain.Resid.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Domain.Resid

open CategoryTheory Limits AlgebraicGeometry

universe u

theorem canonPt_closed {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    {X : Work.GCBasics.Sch K} [AlgebraicGeometry.IsIntegral X.left] (x : X.left)
    {A : Type _} [CommRing A] [IsLocalRing A] [Algebra K A] [Algebra A X.left.functionField]
    [IsScalarTower K A X.left.functionField]
    (ρ : X.left.presheaf.stalk x →+* A) [IsLocalHom ρ]
    (hKA : (Work.GCBasics.specOf K A).hom = CategoryTheory.CategoryStruct.comp
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ))
      (CategoryTheory.CategoryStruct.comp (X.left.fromSpecStalk x) X.hom))
    (hρ : (algebraMap A X.left.functionField).comp ρ =
      algebraMap (X.left.presheaf.stalk x) X.left.functionField) :
    ∃ e : Work.GCBasics.resField X x →ₐ[K] IsLocalRing.ResidueField A,
      ∀ {n : ℕ} (u : X ⟶ (symGeom n).S),
        (symGeom n).divOf (CategoryTheory.CategoryStruct.comp
            (CategoryTheory.CategoryStruct.comp (Work.GCBasics.closedPt (K := K) A)
              (Work.Domain.Resid.canonPt x ρ hKA)) u) =
          Work.SpecLin.DivBase.bc e ((symGeom n).divOf
            (CategoryTheory.CategoryStruct.comp (Work.GCBasics.resPt X x) u)) := by
  -- The residue map on the function field level: `κ(x) →+* κ(A)` induced by `ρ`.
  -- It is a `K`-algebra map, and the closed fibre of the canonical `A`-point is the
  -- base change of the `κ(x)`-point `resPt X x` along it.
  have hklin : ∀ k : K, (Work.Domain.Resid.residueAlgHom x ρ)
      (algebraMap K (Work.GCBasics.resField X x) k) =
        algebraMap K (IsLocalRing.ResidueField A) k := by
    intro k
    let e₀ : Work.GCBasics.resField X x →+* IsLocalRing.ResidueField A :=
      Work.Domain.Resid.residueAlgHom x ρ
    -- `algebraMap K κ(x)` factors through the stalk, along the K-algebra structure
    -- `Spec.preimage (fromSpecStalk x ≫ X.hom) : K ⟶ O_{X,x}`.
    have h2 : algebraMap K (Work.GCBasics.resField X x) k =
        (X.left.residue x).hom ((Spec.preimage (X.left.fromSpecStalk x ≫ X.hom)).hom k) := by
      show ((Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom)).hom) k = _
      rw [show X.left.fromSpecResidueField x =
          Spec.map (X.left.residue x) ≫ X.left.fromSpecStalk x from rfl]
      rw [Category.assoc, Spec.preimage_comp, Spec.preimage_map]
      rfl
    -- `residueAlgHom` computes as `IsLocalRing.residue A ∘ ρ` on the stalk.
    have he : ∀ y, e₀ ((X.left.residue x).hom y) = IsLocalRing.residue A (ρ y) :=
      fun y => RingHom.congr_fun (Work.Domain.Resid.residueAlgHom_comp x ρ) y
    -- `hKA` says precisely that `ρ` is a morphism of `K`-algebras for the structure
    -- on the stalk induced by `X.hom`.
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
  intro n u
  -- The closed point of the canonical `A`-point: the composite
  -- `Spec κ(A) ⟶ Spec A ⟶ Spec O_{X,x} ⟶ X` is the composite
  -- `Spec κ(A) ⟶ Spec κ(x) ⟶ X` of the `κ(x)`-point `resPt X x` with `Spec e`.
  have hpt : Work.GCBasics.closedPt (K := K) A ≫ Work.Domain.Resid.canonPt x ρ hKA =
      Work.GCBasics.RPt.map e (Work.GCBasics.resPt X x) := by
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
  rw [hpt, Work.GCBasics.RPt.map, Category.assoc]
  exact (symGeom n).divOf_map e (CategoryTheory.CategoryStruct.comp
    (Work.GCBasics.resPt X x) u)

end Work.Domain.Resid
