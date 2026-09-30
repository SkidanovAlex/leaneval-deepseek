import Mathlib
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.Kit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.DescentGeom

open CategoryTheory AlgebraicGeometry Limits

/-- Descent of geometric irreducibility along a field extension `k'/k`.

If the base change `A_{k'}` of a `k`-scheme `A` is geometrically irreducible over `k'`, then `A`
is geometrically irreducible over `k`.

The key point is that a test field `K` over `k` need not be a `k'`-algebra; one first extends it to
a field `L` which receives a `k`-algebra map from `k'` (any residue field of `k' ⊗[k] K` works),
uses the hypothesis there, and descends the irreducibility back along the surjection
`Spec L ⟶ Spec K`. -/
theorem geometricallyIrreducible_of_bc {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (A : Work.DescentGeom.Sch k)
    [AlgebraicGeometry.GeometricallyIrreducible (Work.DescentGeom.bc k' A).hom] :
    AlgebraicGeometry.GeometricallyIrreducible A.hom := by
  refine AlgebraicGeometry.GeometricallyIrreducible.mk ?_
  rw [AlgebraicGeometry.geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  -- A field `L` with `k`-algebra maps `k' →+* L` and `K →+* L`, compatible over `k`.
  have hex : ∃ (L : Type u) (_ : Field L) (iL : k' →+* L) (iR : K →+* L),
      iL.comp (algebraMap k k') = iR.comp (algebraMap k K) := by
    let R := TensorProduct k k' K
    haveI : Nontrivial R := inferInstance
    obtain ⟨M, hM⟩ := Ideal.exists_maximal R
    haveI : M.IsMaximal := hM
    refine ⟨R ⧸ M, Ideal.Quotient.field M, ?_, ?_, ?_⟩
    · exact (Ideal.Quotient.mk M).comp
        (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := k') (B := K)).toRingHom
    · exact (Ideal.Quotient.mk M).comp
        (Algebra.TensorProduct.includeRight (R := k) (A := k') (B := K)).toRingHom
    · have h := Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        (R := k) (A := k') (B := K)
      exact congrArg (fun f => (Ideal.Quotient.mk M).comp f) h
  obtain ⟨L, hL, iL, iR, hcompat⟩ := hex
  letI : Field L := hL
  set yL' : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k') :=
    Spec.map (CommRingCat.ofHom iL) with hyL'
  set yK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K)) with hyK
  set ys : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom iR) with hysdef
  have hgeom := AlgebraicGeometry.GeometricallyIrreducible.geometrically_irreducibleSpace
    (f := (bc k' A).hom)
  -- the hypothesis, applied over the test field `L`
  haveI hWL : IrreducibleSpace ↥(pullback (bc k' A).hom yL') :=
    AlgebraicGeometry.pullback_of_geometrically hgeom L yL'
  -- `bc k' A` is the pullback of `A.hom` along `Spec k' ⟶ Spec k`
  have hWL' : IrreducibleSpace
      ↥(pullback (pullback.snd A.hom (Work.Descent.specMap k k')) yL') := hWL
  have e1 := pullbackLeftPullbackSndIso A.hom (Work.Descent.specMap k k') yL'
  haveI h2 : IrreducibleSpace ↥(pullback A.hom (yL' ≫ Work.Descent.specMap k k')) :=
    e1.hom.homeomorph.irreducibleSpace_iff.mp hWL'
  -- the two factorisations of `Spec L ⟶ Spec k` agree
  have h1 : (CommRingCat.ofHom (algebraMap k k') ≫ CommRingCat.ofHom iL)
      = (CommRingCat.ofHom (algebraMap k K) ≫ CommRingCat.ofHom iR) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcompat]
  have hcomp : yL' ≫ Work.Descent.specMap k k' = ys ≫ yK := by
    simp only [hyL', hysdef, hyK, Work.Descent.specMap]
    rw [← Spec.map_comp, ← Spec.map_comp, h1]
  haveI h3 : IrreducibleSpace ↥(pullback A.hom (ys ≫ yK)) := hcomp ▸ h2
  have e2 := pullbackLeftPullbackSndIso A.hom yK ys
  haveI h4 : IrreducibleSpace ↥(pullback (pullback.snd A.hom yK) ys) :=
    e2.hom.homeomorph.irreducibleSpace_iff.mpr h3
  -- `Spec L ⟶ Spec K` is surjective (both are one-point spaces)
  have hysurj : Surjective ys := by
    refine Surjective.mk fun y => ?_
    obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of L)))
    exact ⟨x, Subsingleton.elim _ _⟩
  have hfst : Surjective (pullback.fst (pullback.snd A.hom yK) ys) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback (pullback.snd A.hom yK) ys).flip hysurj
  -- irreducibility descends along the surjection
  have hZ : IsIrreducible (Set.univ : Set ↥(pullback A.hom yK)) := by
    have himg : IsIrreducible ((pullback.fst (pullback.snd A.hom yK) ys) ''
        (Set.univ : Set ↥(pullback (pullback.snd A.hom yK) ys))) :=
      (IrreducibleSpace.isIrreducible_univ ↥(pullback (pullback.snd A.hom yK) ys)).image _
        (pullback.fst (pullback.snd A.hom yK) ys).continuous.continuousOn
    rwa [Set.image_univ, Set.range_eq_univ.mpr hfst.surj] at himg
  exact (irreducibleSpace_def _).mpr hZ

end Work.DescentGeom
