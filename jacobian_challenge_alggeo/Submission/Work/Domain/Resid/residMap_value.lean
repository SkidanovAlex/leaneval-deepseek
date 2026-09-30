import Mathlib
import Submission.Work.Domain.Resid.Setup
import Submission.Work.Domain.Resid.valueOf_api
import Submission.Work.Domain.Resid.rel_resPt
import Submission.Work.GroupChunk.exists_factor_resPt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 4000000
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.Domain.Resid

open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} [SpecLin.DivBase C]

/-- `Work.SpecLin.RPt.map` is `Work.GCBasics.RPt.map`. -/
theorem specLinRPtMap_eq {X : Sch K} {R R' : Type u} [CommRing R] [Algebra K R]
    [CommRing R'] [Algebra K R'] (e : R →ₐ[K] R') (p : RPt X R) :
    SpecLin.RPt.map e p = RPt.map e p := rfl

/-- **VALUE of the residue map**, reduced to the residue-point relation `rel_resPt`. -/
theorem residMap_value_aux {symGeom : ∀ n, SpecLin.SymGeom C n} {g : ℕ}
    (D : ResidData (K := K) symGeom g) {X : Sch K}
    [IsIntegral X.left] [IsLocallyNoetherian X.left]
    (hX : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    {r m : ℕ} (hred : IsReduced X.left)
    (hsep : IsSeparated ((symGeom m).S).hom)
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S) (hm : g ≤ m)
    (H : ∀ (x : X.left) (hx : x ∈ (D.residMap a b hm).domain),
      Rel symGeom a b (resPt X x) (valueOf hred hsep (D.residMap a b hm)
        (D.residMap_isOver a b hm) (resPt X x)
        ((resPt_landsIn_iff X x (D.residMap a b hm).domain).mpr hx)))
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F)
    (hp : RPt.LandsIn p (D.residMap a b hm).domain) :
    Rel symGeom a b p (valueOf hred hsep (D.residMap a b hm)
      (D.residMap_isOver a b hm) p hp) := by
  haveI : IsReduced X.left := hred
  haveI : IsSeparated ((symGeom m).S).hom := hsep
  haveI : ((symGeom m).S).left.IsSeparated := instSchemeIsSeparated
  haveI : (D.residMap a b hm).IsOver (Spec (CommRingCat.of K)) := D.residMap_isOver a b hm
  haveI : (D.residMap a b hm).toPartialMap.IsOver (Spec (CommRingCat.of K)) := inferInstance
  let x := p.left (IsLocalRing.closedPoint F)
  have hxdom : x ∈ (D.residMap a b hm).domain := hp
  have hpx : RPt.LandsIn (resPt X x) (D.residMap a b hm).domain :=
    (resPt_landsIn_iff X x (D.residMap a b hm).domain).mpr hxdom
  have hpx2 : RPt.LandsIn (resPt X x) (D.residMap a b hm).toPartialMap.domain := hpx
  obtain ⟨e, he⟩ := Work.GroupChunk.exists_factor_resPt (K := K) p
  obtain ⟨q₀, hq₀, -⟩ :=
    RPt.factor_of_closed_landsIn (D.residMap a b hm).toPartialMap.domain (resPt X x) hpx2
  have hq' : (RPt.map e q₀) ≫ Opens.ιOver (D.residMap a b hm).toPartialMap.domain
      = RPt.map e (resPt X x) := by
    show specOfMap (K := K) e ≫ q₀ ≫ Opens.ιOver (D.residMap a b hm).toPartialMap.domain
      = RPt.map e (resPt X x)
    rw [hq₀]
    rfl
  have hq : (RPt.map e q₀) ≫ Opens.ιOver (D.residMap a b hm).toPartialMap.domain = p :=
    hq'.trans he.symm
  have hy : RPt.map e (valueOf hred hsep (D.residMap a b hm) (D.residMap_isOver a b hm)
        (resPt X x) hpx) = valueOf hred hsep (D.residMap a b hm) (D.residMap_isOver a b hm) p hp := by
    apply Over.OverMorphism.ext
    simp only [RPt.map, Over.comp_left, Work.GCBasics.specOfMap_left]
    rw [valueOf_left_eq hred hsep _ _ (resPt X x) hpx q₀ hq₀]
    rw [valueOf_left_eq hred hsep _ _ p hp (RPt.map e q₀) hq]
    simp only [RPt.map, Over.comp_left, Work.GCBasics.specOfMap_left]
    exact (Category.assoc _ _ _).symm
  have hp2 : RPt.map e (resPt X x ≫ a) = p ≫ a := by
    show RPt.map e (resPt X x) ≫ a = p ≫ a
    rw [he.symm]
  have hp3 : RPt.map e (resPt X x ≫ b) = p ≫ b := by
    show RPt.map e (resPt X x) ≫ b = p ≫ b
    rw [he.symm]
  have h1 : SpecLin.DivBase.bc e ((symGeom m).divOf (valueOf hred hsep (D.residMap a b hm)
        (D.residMap_isOver a b hm) (resPt X x) hpx))
      = (symGeom m).divOf (valueOf hred hsep (D.residMap a b hm) (D.residMap_isOver a b hm) p hp) := by
    rw [← (symGeom m).divOf_map e, specLinRPtMap_eq]
    exact congrArg _ hy
  have h2 : SpecLin.DivBase.bc e ((symGeom r).divOf (resPt X x ≫ a)) = (symGeom r).divOf (p ≫ a) := by
    rw [← (symGeom r).divOf_map e, specLinRPtMap_eq]
    exact congrArg _ hp2
  have h3 : SpecLin.DivBase.bc e ((symGeom (r + m)).divOf (resPt X x ≫ b))
      = (symGeom (r + m)).divOf (p ≫ b) := by
    rw [← (symGeom (r + m)).divOf_map e, specLinRPtMap_eq]
    exact congrArg _ hp3
  have Hx := H x hxdom
  rw [Rel] at Hx
  have hpr : valueOf hred hsep (D.residMap a b hm) (D.residMap_isOver a b hm) (resPt X x)
        ((resPt_landsIn_iff X x (D.residMap a b hm).domain).mpr hxdom)
      = valueOf hred hsep (D.residMap a b hm) (D.residMap_isOver a b hm) (resPt X x) hpx :=
    valueOf_proof_irrel _ _ _ _ _ _ _
  rw [hpr] at Hx
  rw [Rel]
  have hbc := SpecLin.DivBase.linEquiv_bc e Hx
  rw [SpecLin.DivBase.bc_add] at hbc
  rw [h1, h2, h3] at hbc
  exact hbc

theorem residMap_value {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] {symGeom : ∀ n, Work.SpecLin.SymGeom C n} {g : ℕ}
    (D : Work.Domain.Resid.ResidData (K := K) symGeom g) {X : Work.GCBasics.Sch K}
    [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsLocallyNoetherian X.left]
    (hX : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    {r m : ℕ} (hred : AlgebraicGeometry.IsReduced X.left)
    (hsep : AlgebraicGeometry.IsSeparated ((symGeom m).S).hom)
    (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S) (hm : g ≤ m)
    {F : Type _} [Field F] [Algebra K F] (p : Work.GCBasics.FPt X F)
    (hp : Work.GCBasics.RPt.LandsIn p (D.residMap a b hm).domain) :
    Work.Domain.Resid.Rel symGeom a b p
      (Work.Domain.Resid.valueOf hred hsep (D.residMap a b hm)
        (D.residMap_isOver a b hm) p hp) := by
  exact residMap_value_aux D hX hred hsep a b hm
    (fun x hx => rel_resPt D hred hsep a b hm x hx) p hp

end

end Work.Domain.Resid
