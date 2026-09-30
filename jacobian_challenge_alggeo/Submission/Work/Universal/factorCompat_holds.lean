import Mathlib
import Submission.Work.Universal.Basic
import Submission.Work.Universal.isSeparated_hom_of_grpObj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area UP — the compatibility of the chart maps of `factor`

This file proves `Work.Universal.factorCompat_holds`: the chart maps
`chartMap f i = Σ^g f|_V − Σ^g f(E i)` of the glued group chunk `G D` agree on the
transition domains `U i j`, transported along the transition morphisms `t i j`.

The mathematical content is the key lemma of area KL: on a field point `p : U i j(F)`,
the transition `t i j` sends it to the effective representative of `divOf p − E i + E j`
(`t_value`, `σ_value`), so
`divOf (t i j p) + E i ~ divOf p + E j`;
constancy of `Σ^g f` on linear equivalence classes (`Input.kl`) together with its
additivity (`Input.kl_add`) gives `Σ f(t p) + Σ f(E j) = Σ f(p) + Σ f(E i)`, i.e. the two
chart values agree.

Morphism-level, this is checked on residue-field points, using that a group object in
`Over (Spec K)` over a field is separated (`isSeparated_hom_of_grpObj`), so that morphisms
into `A` out of a reduced scheme are detected by their values on residue-field points
(`Work.GCBasics.hom_ext_of_resPt`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open scoped Work.GCBasics

universe u

namespace Work.Universal

noncomputable section

open Work.GCBasics Work.GroupChunk

variable {K : Type u} [Field K] {C : CurveBasics.Curve K}
  {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
  [D : GroupChunk.Input C P0] [U : Input C P0]
  {A : Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [IsProper A.hom]

/-! ## The effectivity of the base-changed centre divisors -/

theorem factorCompat_bcKF_EDiv_isEffective (i : D.Idx) {F : Type u} [Field F] [Algebra K F] :
    (bcKF (C := C) F (D.EDiv i)).IsEffective :=
  SpecLin.DivBase.isEffective_bc (Algebra.ofId K F) (D.EDiv_isEffective i)

/-! ## The value of `Σᵍ f` at a constant chart -/

theorem factorCompat_constE_sumMap (f : C.toOver ⟶ A) (i : D.Idx) (X : Sch K) {F : Type u}
    [Field F] [Algebra K F] (q : FPt X F) :
    (q ≫ GroupChunk.constE i X) ≫ sumMap D f D.g
      = sumDiv D f (bcKF (C := C) F (D.EDiv i)) (factorCompat_bcKF_EDiv_isEffective (D := D) i)
          D.g (ddeg_bcKF_EDiv D i) :=
  (sumDiv_eq_of_divOf D f _ _ (GroupChunk.constE_divOf i X q)).symm

/-! ## The chart map as a quotient of two values of `Σᵍ f` -/

theorem factorCompat_chartMap_apply (f : C.toOver ⟶ A) (i : D.Idx) {F : Type u} [Field F]
    [Algebra K F] (q : FPt (Opens.toOver D.V) F) :
    q ≫ chartMap (D := D) f i
      = (q ≫ Opens.ιOver D.V ≫ sumMap D f D.g)
        / (q ≫ GroupChunk.constE i (Opens.toOver D.V) ≫ sumMap D f D.g) := by
  simp only [chartMap, div_eq_mul_inv]
  rw [MonObj.comp_mul, GrpObj.comp_inv]

/-! ## The pointwise computation -/

/-- **The pointwise compatibility of the chart maps**, at an arbitrary field point of the
transition domain `U i j`: the value of the `i`-th chart map and the value of the `j`-th chart
map at the transported point agree.  This is the key lemma of area KL. -/
theorem factorCompat_point_key (f : C.toOver ⟶ A) (i j : D.Idx) {F : Type u} [Field F]
    [Algebra K F] (p : FPt (Opens.toOver (GroupChunk.U i j)) F) :
    ((p ≫ Opens.ιOver (GroupChunk.U i j)) ≫ Opens.ιOver D.V ≫ sumMap D f D.g)
        * ((p ≫ (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i)))
            ≫ GroupChunk.constE j (Opens.toOver D.V) ≫ sumMap D f D.g)
      = ((p ≫ (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i)))
            ≫ Opens.ιOver D.V ≫ sumMap D f D.g)
        * ((p ≫ Opens.ιOver (GroupChunk.U i j))
            ≫ GroupChunk.constE i (Opens.toOver D.V) ≫ sumMap D f D.g) := by
  have hp : RPt.LandsIn (p ≫ GroupChunk.Uι i j) (GroupChunk.σ i j).domain := by
    simp only [RPt.LandsIn, Over.comp_left]
    exact GroupChunk.W_le_domain i j
      (GroupChunk.range_Uι_le_W i j ⟨p.left (IsLocalRing.closedPoint F), rfl⟩)
  have ht : p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i
      = GroupChunk.σVal i j (p ≫ GroupChunk.Uι i j) hp :=
    GroupChunk.t_value i j p hp
  have hσ : LinEquiv C ((D.symGeom D.g).divOf (GroupChunk.σVal i j (p ≫ GroupChunk.Uι i j) hp)
        + bcKF (C := C) F (D.EDiv i))
      ((D.symGeom D.g).divOf (p ≫ GroupChunk.Uι i j) + bcKF (C := C) F (D.EDiv j)) :=
    GroupChunk.σ_value i j (p ≫ GroupChunk.Uι i j) hp
  have hlin : LinEquiv C ((D.symGeom D.g).divOf (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i)
        + bcKF (C := C) F (D.EDiv i))
      ((D.symGeom D.g).divOf (p ≫ GroupChunk.Uι i j) + bcKF (C := C) F (D.EDiv j)) := by
    rw [ht]
    exact hσ
  have hU₁ : (p ≫ Opens.ιOver (GroupChunk.U i j)) ≫ Opens.ιOver D.V
      = p ≫ GroupChunk.Uι i j := by
    simp only [GroupChunk.Uι, Category.assoc]
  have hU₂ : (p ≫ (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i))) ≫ Opens.ιOver D.V
      = p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i := by
    simp only [GroupChunk.Uι, Category.assoc]
  have hN₁ : (p ≫ Opens.ιOver (GroupChunk.U i j)) ≫ Opens.ιOver D.V ≫ sumMap D f D.g
      = sumDiv D f (D.divOf D.g (p ≫ GroupChunk.Uι i j))
          ((D.symGeom D.g).divOf_isEffective (p ≫ GroupChunk.Uι i j)) D.g
          (ddeg_divOf D (p ≫ GroupChunk.Uι i j)) := by
    rw [← Category.assoc, hU₁, ← sumMap_fpt D f D.g (p ≫ GroupChunk.Uι i j)]
  have hN₂ : (p ≫ (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i))) ≫ Opens.ιOver D.V
        ≫ sumMap D f D.g
      = sumDiv D f (D.divOf D.g (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i))
          ((D.symGeom D.g).divOf_isEffective (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i)) D.g
          (ddeg_divOf D (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i)) := by
    rw [← Category.assoc, hU₂, ← sumMap_fpt D f D.g (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i)]
  have hD₁ : (p ≫ Opens.ιOver (GroupChunk.U i j)) ≫ GroupChunk.constE i (Opens.toOver D.V)
        ≫ sumMap D f D.g
      = sumDiv D f (bcKF (C := C) F (D.EDiv i)) (factorCompat_bcKF_EDiv_isEffective (D := D) i)
          D.g (ddeg_bcKF_EDiv D i) := by
    rw [← Category.assoc]
    exact factorCompat_constE_sumMap f i (Opens.toOver D.V) (p ≫ Opens.ιOver (GroupChunk.U i j))
  have hD₂ : (p ≫ (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i)))
        ≫ GroupChunk.constE j (Opens.toOver D.V) ≫ sumMap D f D.g
      = sumDiv D f (bcKF (C := C) F (D.EDiv j)) (factorCompat_bcKF_EDiv_isEffective (D := D) j)
          D.g (ddeg_bcKF_EDiv D j) := by
    rw [← Category.assoc]
    exact factorCompat_constE_sumMap f j (Opens.toOver D.V)
      (p ≫ (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i)))
  have hsum₁ := Input.kl_add (D := D) f (D.divOf D.g (p ≫ GroupChunk.Uι i j))
    (bcKF (C := C) F (D.EDiv j))
    ((D.symGeom D.g).divOf_isEffective (p ≫ GroupChunk.Uι i j))
    (factorCompat_bcKF_EDiv_isEffective (D := D) j) D.g D.g
    (ddeg_divOf D (p ≫ GroupChunk.Uι i j)) (ddeg_bcKF_EDiv D j)
    (((D.symGeom D.g).divOf_isEffective (p ≫ GroupChunk.Uι i j)).add
      (factorCompat_bcKF_EDiv_isEffective (D := D) j))
  have hsum₂ := Input.kl_add (D := D) f (D.divOf D.g (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i))
    (bcKF (C := C) F (D.EDiv i))
    ((D.symGeom D.g).divOf_isEffective (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i))
    (factorCompat_bcKF_EDiv_isEffective (D := D) i) D.g D.g
    (ddeg_divOf D (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i)) (ddeg_bcKF_EDiv D i)
    (((D.symGeom D.g).divOf_isEffective (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i)).add
      (factorCompat_bcKF_EDiv_isEffective (D := D) i))
  have hkl := Input.kl (D := D) f
    (D.divOf D.g (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i) + bcKF (C := C) F (D.EDiv i))
    (D.divOf D.g (p ≫ GroupChunk.Uι i j) + bcKF (C := C) F (D.EDiv j))
    (((D.symGeom D.g).divOf_isEffective (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i)).add
      (factorCompat_bcKF_EDiv_isEffective (D := D) i))
    (((D.symGeom D.g).divOf_isEffective (p ≫ GroupChunk.Uι i j)).add
      (factorCompat_bcKF_EDiv_isEffective (D := D) j))
    (D.g + D.g)
    (ddeg_add (ddeg_divOf D (p ≫ GroupChunk.t i j ≫ GroupChunk.Uι j i)) (ddeg_bcKF_EDiv D i))
    (ddeg_add (ddeg_divOf D (p ≫ GroupChunk.Uι i j)) (ddeg_bcKF_EDiv D j))
    hlin
  rw [hN₁, hD₂, ← hsum₁, ← hkl, hsum₂, ← hN₂, ← hD₁]

/-- **The pointwise compatibility of the chart maps**, stated as the equality of the two
morphisms after evaluation at a field point of `U i j`. -/
theorem factorCompat_point (f : C.toOver ⟶ A) (i j : D.Idx) {F : Type u} [Field F]
    [Algebra K F] (p : FPt (Opens.toOver (GroupChunk.U i j)) F) :
    p ≫ Opens.ιOver (GroupChunk.U i j) ≫ chartMap (D := D) f i
      = p ≫ (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i)) ≫ chartMap (D := D) f j := by
  have hL : p ≫ Opens.ιOver (GroupChunk.U i j) ≫ chartMap (D := D) f i
      = ((p ≫ Opens.ιOver (GroupChunk.U i j)) ≫ Opens.ιOver D.V ≫ sumMap D f D.g)
        / ((p ≫ Opens.ιOver (GroupChunk.U i j)) ≫ GroupChunk.constE i (Opens.toOver D.V)
            ≫ sumMap D f D.g) := by
    rw [← Category.assoc, factorCompat_chartMap_apply]
  have hR : p ≫ (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i)) ≫ chartMap (D := D) f j
      = ((p ≫ (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i))) ≫ Opens.ιOver D.V
            ≫ sumMap D f D.g)
        / ((p ≫ (GroupChunk.t i j ≫ Opens.ιOver (GroupChunk.U j i)))
            ≫ GroupChunk.constE j (Opens.toOver D.V) ≫ sumMap D f D.g) := by
    rw [← Category.assoc, factorCompat_chartMap_apply]
  rw [hL, hR, div_eq_div_iff_mul_eq_mul]
  exact factorCompat_point_key f i j p

/-! ## The compatibility of the chart maps -/

theorem factorCompat_holds {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : Work.AbVar.Point C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] [U : Work.Universal.Input C P0]
    {A : Work.GCBasics.Sch K} [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    [IsProper A.hom]
    (f : C.toOver ⟶ A) : Work.Universal.factorCompat (D := D) f := by
  haveI : AlgebraicGeometry.IsSeparated A.hom := isSeparated_hom_of_grpObj A
  intro i j
  haveI : IsReduced (Opens.toOver D.V).left := inferInstanceAs (IsReduced (D.V : Scheme))
  haveI : IsReduced (Opens.toOver (GroupChunk.U i j)).left :=
    inferInstanceAs (IsReduced (GroupChunk.U i j : Scheme))
  refine Work.GCBasics.hom_ext_of_resPt _ _ ?_
  intro y
  exact factorCompat_point (D := D) f i j (Work.GCBasics.resPt _ y)

end

end Work.Universal
