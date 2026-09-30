import Mathlib
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.quotMap_eq_iff_exists_perm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open scoped Work.GCBasics

universe u

namespace Work.Charts

/-- **Point lifting along a pullback of `K`-schemes.**  If `f : X ⟶ Z` and `g : Y ⟶ Z` are
morphisms of `K`-schemes and `x : X`, `y : Y` are points with the same image in `Z`, then there
is a point `z` of the fibre product `X ×_Z Y` projecting onto `x` and `y`.

This is the `Over (Spec K)`-form of `AlgebraicGeometry.Scheme.exists_preimage_of_isPullback`,
obtained by applying the (limit-preserving) forgetful functor `Over (Spec K) ⥤ Scheme`. -/
private theorem exists_preimage_pullback_over {K : Type u} [Field K] {X Y Z : Work.GCBasics.Sch K}
    (f : X ⟶ Z) (g : Y ⟶ Z) (x : X.left) (y : Y.left) (hxy : f.left x = g.left y) :
    ∃ z : (pullback f g).left, (pullback.fst f g).left z = x ∧ (pullback.snd f g).left z = y := by
  have hpb : IsPullback (Over.Hom.left (pullback.fst f g)) (Over.Hom.left (pullback.snd f g))
      (Over.Hom.left f) (Over.Hom.left g) :=
    (IsPullback.of_hasPullback f g).map (Over.forget (Spec (CommRingCat.of K)))
  obtain ⟨z, hz1, hz2⟩ := Scheme.exists_preimage_of_isPullback hpb x y hxy
  exact ⟨z, hz1, hz2⟩

/-- **The fibres of the quotient map `C^n ⟶ Sym^n C` are the `S_n`-orbits** (topological form).

Two points of the underlying topological space of the `n`-fold product `C^n` with the same image
under the quotient map `quotMap C n : C^n ⟶ Sym^n C` differ by a permutation of the coordinates.

The point-level statement `quotMap_eq_iff_exists_perm` compares *field points* of `C^n` over a
common field.  Two arbitrary points `x`, `x'` in one fibre are promoted to field points over the
*common* residue field `κ(z)` of a point `z` of the fibre product `C^n ×_{Sym^n C} C^n` lying
above `(x, x')` (`exists_preimage_pullback_over`), whose two projections have equal image simply
because `pullback.fst ≫ quotMap = pullback.snd ≫ quotMap`. -/
theorem exists_perm_of_quotMap_eq {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} (n : ℕ)
    [Work.SpecLin.DivBase C] [Work.SpecLin.SymGeom C n]
    {x x' : (Work.Charts.Cprod C n).left}
    (h : (Work.Charts.quotMap C n).left x = (Work.Charts.quotMap C n).left x') :
    ∃ σ : Equiv.Perm (Fin n), (Work.SymQuot.permIso C.toOver σ).hom.left x = x' := by
  obtain ⟨z, hz1, hz2⟩ := exists_preimage_pullback_over (Work.Charts.quotMap C n)
    (Work.Charts.quotMap C n) x x' h
  let P := pullback (Work.Charts.quotMap C n) (Work.Charts.quotMap C n)
  let F := Work.GCBasics.resField P z
  let a : Work.GCBasics.FPt (Work.Charts.Cprod C n) F :=
    Work.GCBasics.resPt P z ≫ pullback.fst (Work.Charts.quotMap C n) (Work.Charts.quotMap C n)
  let b : Work.GCBasics.FPt (Work.Charts.Cprod C n) F :=
    Work.GCBasics.resPt P z ≫ pullback.snd (Work.Charts.quotMap C n) (Work.Charts.quotMap C n)
  have hq : Work.Charts.ptComp a (Work.Charts.quotMap C n) =
      Work.Charts.ptComp b (Work.Charts.quotMap C n) := by
    simp only [Work.Charts.ptComp_apply]
    dsimp only [a, b, P]
    rw [Category.assoc, Category.assoc, CategoryTheory.Limits.pullback.condition]
  obtain ⟨σ, hσ⟩ := (Work.Charts.quotMap_eq_iff_exists_perm (C := C) n (x := a) (y := b)).mp hq
  refine ⟨σ, ?_⟩
  let c : ↥(Over.left (Work.GCBasics.specOf K F)) := IsLocalRing.closedPoint F
  have hbl : (Over.Hom.left b) c = x' := by
    dsimp only [b, P]
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    rw [show (Over.Hom.left (Work.GCBasics.resPt
        (pullback (Work.Charts.quotMap C n) (Work.Charts.quotMap C n)) z)) c = z from
      Work.GCBasics.resPt_apply _ _ _]
    exact hz2
  have hal : (Over.Hom.left (Work.Charts.ptComp a (Work.SymQuot.permIso C.toOver σ).hom)) c
      = (Over.Hom.left (Work.SymQuot.permIso C.toOver σ).hom) x := by
    dsimp only [a, Work.Charts.ptComp]
    rw [Over.comp_left, Over.comp_left, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    rw [show (Over.Hom.left (Work.GCBasics.resPt
        (pullback (Work.Charts.quotMap C n) (Work.Charts.quotMap C n)) z)) c = z from
      Work.GCBasics.resPt_apply _ _ _]
    rw [hz1]
  have hc := congrArg (fun (φ : Work.GCBasics.FPt (Work.Charts.Cprod C n) F) =>
      φ.left c) hσ
  rw [hbl, hal] at hc
  exact hc.symm

end Work.Charts
