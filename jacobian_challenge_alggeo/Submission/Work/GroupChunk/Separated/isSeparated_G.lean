import Mathlib
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Transitions
import Submission.Work.GroupChunk.Gluing.Data
import Submission.Work.GroupChunk.t_inv
import Submission.Work.GroupChunk.landsIn_U_iff
import Submission.Work.GroupChunk.Gluing.Transitions
import Submission.Work.GroupChunk.AJSym
import Submission.Work.SpecLin.All
import Submission.Work.GroupChunk.Separated.valuativeCriterion_Uniqueness_of_pts
import Submission.Work.GroupChunk.Separated.exists_chart_factor
import Submission.Work.GroupChunk.Separated.picOf_closed_eq_of_picOf_gen_eq
import Submission.Work.GroupChunk.Separated.isDominant_genPt
import Submission.Work.GroupChunk.Separated.tq_chart_compat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.GroupChunk.Separated

universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry MonoidalCategory
open Work.GCBasics

/-! ## The main pointwise statement -/

section

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
  {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
  [Work.SpecLin.DivBase C] [D : Work.GroupChunk.Input C P0]

theorem G_eq_of_generic_eq {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    {p q : RPt (GSch D) R}
    (h : RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) p
       = RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) q) :
    p = q := by
  have hgen : genPt (K := K) R ≫ p = genPt (K := K) R ≫ q := h
  obtain ⟨i, a, hpa⟩ := exists_chart_factor (K := K) D p
  obtain ⟨j, c, hqc⟩ := exists_chart_factor (K := K) D q
  -- class agreement at the generic point
  have hcls : D.picOf i ((genPt (K := K) R ≫ a) ≫ Opens.ιOver D.V)
      = D.picOf j ((genPt (K := K) R ≫ c) ≫ Opens.ιOver D.V) := by
    rw [← Work.GroupChunk.Input.eq_iff_class D i j (genPt (K := K) R ≫ a) (genPt (K := K) R ≫ c)]
    simp only [Category.assoc]
    rw [hpa, hqc, hgen]
  simp only [Category.assoc] at hcls
  -- class agreement at the closed point
  have hclsd : D.picOf i (closedPt (K := K) R ≫ (a ≫ Opens.ιOver D.V))
      = D.picOf j (closedPt (K := K) R ≫ (c ≫ Opens.ιOver D.V)) :=
    picOf_closed_eq_of_picOf_gen_eq D hcls
  -- the closed point of `a` lands in `U i j`
  have hland : RPt.LandsIn (closedPt (K := K) R ≫ a) (U i j) := by
    rw [landsIn_U_iff (D := D) i j (closedPt (K := K) R ≫ a)]
    refine ⟨(closedPt (K := K) R ≫ c) ≫ Opens.ιOver D.V,
      landsIn_V_ιOver (D := D) (closedPt (K := K) R ≫ c), ?_⟩
    simp only [Category.assoc] at hclsd ⊢
    exact hclsd.symm
  have hland_a : RPt.LandsIn a (U i j) := by
    have h1 : (Over.Hom.left (closedPt (K := K) R ≫ a))
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))
        = (Over.Hom.left a) (IsLocalRing.closedPoint R) := by
      calc (Over.Hom.left (closedPt (K := K) R ≫ a))
            (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))
          = (Over.Hom.left (closedPt (K := K) R) ≫ Over.Hom.left a)
            (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) := by
              rw [Over.comp_left]
        _ = (Over.Hom.left a) ((Over.Hom.left (closedPt (K := K) R))
              (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
              AlgebraicGeometry.Scheme.Hom.comp_apply _ _ _
        _ = (Over.Hom.left a) (IsLocalRing.closedPoint R) :=
              congrArg _ (closedPt_apply (K := K) R)
    rw [RPt.landsIn_iff, ← h1]
    exact hland
  obtain ⟨a', ha', -⟩ := RPt.factor_of_closed_landsIn (U i j) a hland_a
  have key : (genPt (K := K) R ≫ a') ≫ Uι i j = genPt (K := K) R ≫ (a ≫ Opens.ιOver D.V) := by
    have hAC : (genPt (K := K) R ≫ a') ≫ Opens.ιOver (U i j) = genPt (K := K) R ≫ a := by
      rw [Category.assoc, ha']
    rw [Uι_def]
    rw [show (genPt (K := K) R ≫ a') ≫ (Opens.ιOver (U i j) ≫ Opens.ιOver D.V)
          = ((genPt (K := K) R ≫ a') ≫ Opens.ιOver (U i j)) ≫ Opens.ιOver D.V from
        (Category.assoc _ _ _).symm]
    rw [hAC, Category.assoc]
  have htq : a' ≫ tq i j = c := by
    haveI : IsReduced (specOf K R).left := by
      change IsReduced (Spec (CommRingCat.of R))
      infer_instance
    haveI : IsDominant (genPt (K := K) R).left := isDominant_genPt (K := K) R
    suffices hgf : genPt (K := K) R ≫ (a' ≫ tq i j) = genPt (K := K) R ≫ c by
      apply Over.OverMorphism.ext
      refine AlgebraicGeometry.ext_of_isDominant_of_isSeparated
        (X := (specOf K R).left) (Y := (Opens.toOver D.V).left)
        (Z := Spec (CommRingCat.of K)) (W := (specOf K (FractionRing R)).left)
        (f := (a' ≫ tq i j).left) (g := c.left)
        (s := (Opens.toOver D.V).hom) ?_ (genPt (K := K) R).left ?_
      · rw [Over.w (a' ≫ tq i j), Over.w c]
      · simpa only [Over.comp_left] using congrArg Over.Hom.left hgf
    apply picOf_inj_V (D := D) j
    have hA : picOfV (D := D) j (genPt (K := K) R ≫ (a' ≫ tq i j))
        = D.picOf j ((genPt (K := K) R ≫ a') ≫ tq i j ≫ Opens.ιOver D.V) := by
      simp only [picOfV, Category.assoc]
    have hB : D.picOf j ((genPt (K := K) R ≫ a') ≫ tq i j ≫ Opens.ιOver D.V)
        = D.picOf i (genPt (K := K) R ≫ a ≫ Opens.ιOver D.V) := by
      rw [tq_picOf (D := D) i j (genPt (K := K) R ≫ a')]
      exact congrArg (D.picOf i) key
    rw [hA, hB]
    simpa only [picOfV, Category.assoc] using hcls
  rw [← hpa, ← hqc]
  calc a ≫ chartH D i = (a' ≫ Opens.ιOver (U i j)) ≫ chartH D i := by rw [ha']
    _ = a' ≫ (Opens.ιOver (U i j) ≫ chartH D i) := by rw [Category.assoc]
    _ = a' ≫ (tq i j ≫ chartH D j) := by rw [tq_chart_compat D i j]
    _ = (a' ≫ tq i j) ≫ chartH D j := by rw [Category.assoc]
    _ = c ≫ chartH D j := by rw [htq]

end

/-! ## The target theorem -/

theorem isSeparated_G {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0)
    [QuasiSeparated (Work.GroupChunk.GSch D).hom] :
    IsSeparated (Work.GroupChunk.GSch D).hom := by
  haveI : Work.GroupChunk.Input C P0 := D
  have hkey : ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
      (p q : RPt (GSch D) R),
      RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) p
        = RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) q → p = q := by
    intro R _ _ _ _ p q h
    exact G_eq_of_generic_eq (D := D) h
  exact AlgebraicGeometry.IsSeparated.of_valuativeCriterion (GSch D).hom
    (valuativeCriterion_Uniqueness_of_pts (GSch D) hkey)

end Work.GroupChunk.Separated
