/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — points of the glued group chunk

Every field point of the glued scheme `GSch D` factors through a chart, and two chart points
have the same image in `GSch D` exactly when they have the same divisor class.  These are the
two point-level properties of the gluing.

**Formalisation note.**  `Scheme.GlueData.fpt_eq_iff` is stated for an abstract glue datum
`D`, so when it is instantiated at the concrete `def` `glueScheme D` the *types* of the
objects it produces mention `(glueScheme D).V (i, j)`, whose type is only visible after
unfolding the `def` `glueScheme`.  Tactics (`rw`, `simp`) elaborate at `reducible`
transparency and therefore cannot see through `def`s; the specialised statement
`fpt_eq_iff_glue` below restates the result with the `abbrev` definitions `Usch`, `Uinc`,
`trSch` of `Submission/Work/GroupChunk/Gluing/Data.lean`, which *do* unfold, so that the
proof of `chart_eq_iff` can proceed by rewriting.
-/
import Mathlib
import Submission.Work.GroupChunk.Gluing.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K]
variable {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
  [D : Input C P0]

/-- `Scheme.GlueData.fpt_eq_iff` for the concrete glue datum `glueScheme D`, with all the
auxiliary data put in the `abbrev`-level form of `Data.lean`. -/
theorem fpt_eq_iff_glue (D : Input C P0) (i j : D.Idx) {F : Type u} [Field F]
    (p q : Spec (CommRingCat.of F) ⟶ Vsch D) :
    p ≫ (glueScheme D).ι i = q ≫ (glueScheme D).ι j ↔
      ∃ r : Spec (CommRingCat.of F) ⟶ Usch D i j,
        r ≫ Uinc D i j = p ∧ r ≫ trSch D i j ≫ Uinc D j i = q :=
  Work.GCBasics.Scheme.GlueData.fpt_eq_iff (glueScheme D) i j p q

/-- The charts of `glueScheme D` are open immersions.

This is a restatement of Mathlib's `Scheme.GlueData.ι_isOpenImmersion` at the concrete glue
datum `glueScheme D`: instance search cannot find that instance directly, because its type
mentions `(glueScheme D).J`, which is only visible after unfolding the `def` `glueScheme`. -/
theorem isOpenImmersion_ι_glue (D : Input C P0) (i : D.Idx) :
    IsOpenImmersion ((glueScheme D).ι i) :=
  Scheme.GlueData.ι_isOpenImmersion (glueScheme D) i

theorem chart_factor {F : Type u} [Field F] [Algebra K F] (p : FPt (GSch D) F) :
    ∃ (i : D.Idx) (q : FPt (Opens.toOver D.V) F), q ≫ chartH D i = p := by
  obtain ⟨i, q, hq⟩ := fpt_exists_factor (glueScheme D) p.left
  have hhom : q ≫ (Opens.toOver D.V).hom = (specOf K F).hom := by
    rw [← gluedHom_π D i, ← Category.assoc, hq]
    exact Over.w p
  refine ⟨i, Over.homMk q hhom, ?_⟩
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  change q ≫ (glueScheme D).ι i = p.left
  exact hq

theorem chart_eq_iff (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p q : FPt (Opens.toOver D.V) F) :
    p ≫ chartH D i = q ≫ chartH D j ↔
      D.picOf i (p ≫ Opens.ιOver D.V) = D.picOf j (q ≫ Opens.ιOver D.V) := by
  constructor
  · intro h
    have hleft : p.left ≫ (glueScheme D).ι i = q.left ≫ (glueScheme D).ι j := by
      have h1 := congrArg Over.Hom.left h
      rw [Over.comp_left, Over.comp_left] at h1
      simp only [chartH_left] at h1
      exact h1
    obtain ⟨r, hr1, hr2⟩ := (fpt_eq_iff_glue D i j p.left q.left).mp hleft
    have hrhom : r ≫ (Opens.toOver (U i j)).hom = (specOf K F).hom := by
      have h2 : r ≫ (Opens.toOver (U i j)).hom
          = (r ≫ Uinc D i j) ≫ (Opens.toOver D.V).hom := by
        rw [show (Opens.toOver (U i j)).hom
            = Uinc D i j ≫ (Opens.toOver D.V).hom from rfl]
        exact Category.assoc r (Uinc D i j) (Opens.toOver D.V).hom |>.symm
      rw [h2, hr1]
      exact Over.w p
    set r' : FPt (Opens.toOver (U i j)) F := Over.homMk r hrhom with hr'def
    have hr'1 : r' ≫ Opens.ιOver (U i j) = p := by
      rw [hr'def]
      apply Over.OverMorphism.ext
      rw [Over.comp_left]
      change r ≫ (U i j).ι = p.left
      exact hr1
    have hr'2 : r' ≫ tr i j ≫ Opens.ιOver (U j i) = q := by
      rw [hr'def]
      apply Over.OverMorphism.ext
      rw [Over.comp_left, Over.comp_left]
      change r ≫ (tr i j).left ≫ (U j i).ι = q.left
      exact hr2
    have hA : D.picOf i (p ≫ Opens.ιOver D.V) = D.picOf i (r' ≫ Uι i j) := by
      rw [← hr'1, Uι_def, ← Category.assoc]
    have hB : D.picOf i (r' ≫ Uι i j) = D.picOf j (r' ≫ tr i j ≫ Uι j i) :=
      (tr_cls i j r').symm
    have hC : D.picOf j (r' ≫ tr i j ≫ Uι j i) = D.picOf j (q ≫ Opens.ιOver D.V) := by
      rw [← hr'2, Uι_def]
      simp only [Category.assoc]
    rw [hA, hB, hC]
  · intro hcls
    have hin : D.InChart j (D.picOf i (p ≫ Opens.ιOver D.V)) := by
      refine ⟨q ≫ Opens.ιOver D.V, landsIn_V_ιOver q, ?_⟩
      show D.picOf j (q ≫ Opens.ιOver D.V) = D.picOf i (p ≫ Opens.ιOver D.V)
      exact hcls.symm
    have hpij : RPt.LandsIn p (U i j) := (landsIn_U_iff i j p).mpr hin
    obtain ⟨r', hr'1, -⟩ := FPt.factor_of_landsIn (U i j) p hpij
    have hqeq : r' ≫ tr i j ≫ Opens.ιOver (U j i) = q := by
      refine picOf_inj_V j ?_
      show D.picOf j ((r' ≫ tr i j ≫ Opens.ιOver (U j i)) ≫ Opens.ιOver D.V)
        = D.picOf j (q ≫ Opens.ιOver D.V)
      have h1 : D.picOf j ((r' ≫ tr i j ≫ Opens.ιOver (U j i)) ≫ Opens.ιOver D.V)
          = D.picOf i (r' ≫ Uι i j) := by
        rw [show (r' ≫ tr i j ≫ Opens.ιOver (U j i)) ≫ Opens.ιOver D.V
            = r' ≫ tr i j ≫ Uι j i from by rw [Uι_def]; simp only [Category.assoc]]
        exact tr_cls i j r'
      have h2 : D.picOf i (r' ≫ Uι i j)
          = D.picOf i (r' ≫ Opens.ιOver (U i j) ≫ Opens.ιOver D.V) := by
        rw [Uι_def]
      have h3 : D.picOf i (r' ≫ Opens.ιOver (U i j) ≫ Opens.ιOver D.V)
          = D.picOf i (p ≫ Opens.ιOver D.V) := by
        rw [show r' ≫ Opens.ιOver (U i j) ≫ Opens.ιOver D.V
            = (r' ≫ Opens.ιOver (U i j)) ≫ Opens.ιOver D.V from
              (Category.assoc _ _ _).symm, hr'1]
      rw [h1, h2, h3, hcls]
    have hleft : p.left ≫ (glueScheme D).ι i = q.left ≫ (glueScheme D).ι j := by
      apply (fpt_eq_iff_glue D i j p.left q.left).mpr
      refine ⟨r'.left, ?_, ?_⟩
      · show r'.left ≫ Uinc D i j = p.left
        exact congrArg Over.Hom.left hr'1
      · show r'.left ≫ trSch D i j ≫ Uinc D j i = q.left
        exact congrArg Over.Hom.left hqeq
    apply Over.OverMorphism.ext
    show p.left ≫ (glueScheme D).ι i = q.left ≫ (glueScheme D).ι j
    exact hleft

end

end Work.GroupChunk
