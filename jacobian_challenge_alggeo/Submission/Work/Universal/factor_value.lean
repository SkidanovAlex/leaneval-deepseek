/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area UP — the value of `factor` on a point of `G D`

For a morphism `f : C.toOver ⟶ A` into a commutative group object and a field point
`p : G D (F)` of the glued group chunk whose class `cls p` is the class of `D₁ - D₂`,
the value `p ≫ factor f` of the glued morphism `factor f` is the quotient
`Σ f(D₁) / Σ f(D₂)` of the sums of `f` over `D₁` and `D₂`.

The proof factors `p` through a chart `V` of `G D` (`Glued.factor`), so that `factor f` is
evaluated by its chart formula `chartMap f i = Σ^g f / Σ^g f(E i)`; the class of the chart
point `q` is `picOf i q = [divOf q - E i]`, so the hypothesis says
`divOf q + D₂ ~ D₁ + E i`, and the key lemma of area KL (`Input.kl` for constancy on linear
equivalence classes, `Input.kl_add` for additivity) transfers this to the sums.
-/
import Mathlib
import Submission.Work.Universal.Factor
import Submission.Work.Universal.sumDiv_ptDiv
import Submission.Work.Universal.sumDiv_P0Div

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


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

theorem factor_value {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : Work.AbVar.Point C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] [U : Work.Universal.Input C P0]
    {A : Work.GCBasics.Sch K} [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    [IsProper A.hom]
    (f : C.toOver ⟶ A) {F : Type _} [Field F] [Algebra K F] (p : Work.GCBasics.FPt U.glued.G F)
    (D₁ D₂ : Work.GCBasics.Dv C F) (h₁ : D₁.IsEffective) (h₂ : D₂.IsEffective) (n : ℕ)
    (h₁n : Work.GCBasics.Ddeg C F D₁ = (n : ℤ)) (h₂n : Work.GCBasics.Ddeg C F D₂ = (n : ℤ))
    (hc : U.glued.cls p = Work.Universal.mkCls D₁ D₂ n h₁n h₂n) :
    CategoryTheory.CategoryStruct.comp p (Work.Universal.factor (D := D) f)
      = Work.Universal.divPt (Work.Universal.sumDiv D f D₁ h₁ n h₁n)
          (Work.Universal.sumDiv D f D₂ h₂ n h₂n) := by
  classical
  -- Factor the point `p` through a chart of `G D`.
  obtain ⟨i, q, hq⟩ := U.glued.factor p
  rw [← hq, Category.assoc, factor_eq_chartMap (D := D) f i]
  -- Evaluate `factor f` on the chart: `chartMap f i = Σ^g f / Σ^g f(E i)`.
  rw [factorCompat_chartMap_apply (D := D) f i q]
  -- Both `Σᵍ f` values are sums over divisors (`sumMap_fpt`, `constE_divOf`).
  have hN : q ≫ Opens.ιOver D.V ≫ sumMap D f D.g
      = sumDiv D f (D.divOf D.g (q ≫ Opens.ιOver D.V))
          ((D.symGeom D.g).divOf_isEffective (q ≫ Opens.ιOver D.V)) D.g
          (ddeg_divOf D (q ≫ Opens.ιOver D.V)) := by
    rw [← Category.assoc, ← sumMap_fpt D f D.g (q ≫ Opens.ιOver D.V)]
  have hD : q ≫ GroupChunk.constE i (Opens.toOver D.V) ≫ sumMap D f D.g
      = sumDiv D f (bcKF (C := C) F (D.EDiv i))
          (factorCompat_bcKF_EDiv_isEffective (D := D) i) D.g (ddeg_bcKF_EDiv D i) := by
    rw [← Category.assoc]
    exact factorCompat_constE_sumMap f i (Opens.toOver D.V) q
  rw [hN, hD]
  -- The class of `p` is the class of `divOf q - E i`, by the chart formula for `cls`.
  have hcls : U.glued.cls p = D.picOf i (q ≫ Opens.ιOver D.V) :=
    U.glued.cls_eq_picOf (D := D) hq
  have hlin : LinEquiv C
      (D.divOf D.g (q ≫ Opens.ιOver D.V) - bcKF (C := C) F (D.EDiv i)) (D₁ - D₂) := by
    have h := hcls.symm.trans hc
    rw [Input.picOf_def] at h
    have hl := (Pic0.mk_eq_iff
      (ddeg_sub_divOf D.symGeom D.g (q ≫ Opens.ιOver D.V) (D.EF i))
      (ddeg_sub_zero h₁n h₂n)).mp h
    convert hl using 1
    rw [show (D.symGeom D.g).divOf (D.EF i) = bcKF (C := C) F (D.EDiv i)
      from Input.EF_divOf (D := D) i]
  -- Rewrite the linear equivalence as `divOf q + D₂ ~ D₁ + E i`.
  have hlin' : LinEquiv C (D.divOf D.g (q ≫ Opens.ιOver D.V) + D₂)
      (bcKF (C := C) F (D.EDiv i) + D₁) := by
    have h := (LinEquiv.add_iff
      (D.divOf D.g (q ≫ Opens.ιOver D.V) - bcKF (C := C) F (D.EDiv i))
      (D₁ - D₂) (bcKF (C := C) F (D.EDiv i) + D₂)).mpr hlin
    convert h using 1 <;> abel
  -- The key lemma of area KL: constancy on linear equivalence classes.
  have hkl : sumDiv D f (D.divOf D.g (q ≫ Opens.ιOver D.V) + D₂)
        (((D.symGeom D.g).divOf_isEffective (q ≫ Opens.ιOver D.V)).add h₂) (D.g + n)
        (ddeg_add (ddeg_divOf D (q ≫ Opens.ιOver D.V)) h₂n)
      = sumDiv D f (bcKF (C := C) F (D.EDiv i) + D₁)
        ((factorCompat_bcKF_EDiv_isEffective (D := D) i).add h₁) (D.g + n)
        (ddeg_add (ddeg_bcKF_EDiv D i) h₁n) :=
    Input.kl (D := D) f _ _ _ _ (D.g + n) _ _ hlin'
  -- Additivity of the sum (`Input.kl_add`) on both sides.
  have haddA : sumDiv D f (D.divOf D.g (q ≫ Opens.ιOver D.V) + D₂)
        (((D.symGeom D.g).divOf_isEffective (q ≫ Opens.ιOver D.V)).add h₂) (D.g + n)
        (ddeg_add (ddeg_divOf D (q ≫ Opens.ιOver D.V)) h₂n)
      = sumDiv D f (D.divOf D.g (q ≫ Opens.ιOver D.V))
          ((D.symGeom D.g).divOf_isEffective (q ≫ Opens.ιOver D.V)) D.g
          (ddeg_divOf D (q ≫ Opens.ιOver D.V)) * sumDiv D f D₂ h₂ n h₂n :=
    Input.kl_add (D := D) f _ _ _ _ D.g n _ _ _
  have haddB : sumDiv D f (bcKF (C := C) F (D.EDiv i) + D₁)
        ((factorCompat_bcKF_EDiv_isEffective (D := D) i).add h₁) (D.g + n)
        (ddeg_add (ddeg_bcKF_EDiv D i) h₁n)
      = sumDiv D f (bcKF (C := C) F (D.EDiv i))
          (factorCompat_bcKF_EDiv_isEffective (D := D) i) D.g (ddeg_bcKF_EDiv D i)
        * sumDiv D f D₁ h₁ n h₁n :=
    Input.kl_add (D := D) f _ _ _ _ D.g n _ _ _
  -- Combine: `Σf(divOf q) · Σf(D₂) = Σf(D₁) · Σf(E i)` in the commutative group `A(F)`.
  have key : sumDiv D f (D.divOf D.g (q ≫ Opens.ιOver D.V))
        ((D.symGeom D.g).divOf_isEffective (q ≫ Opens.ιOver D.V)) D.g
        (ddeg_divOf D (q ≫ Opens.ιOver D.V)) * sumDiv D f D₂ h₂ n h₂n
      = sumDiv D f D₁ h₁ n h₁n
        * sumDiv D f (bcKF (C := C) F (D.EDiv i))
          (factorCompat_bcKF_EDiv_isEffective (D := D) i) D.g (ddeg_bcKF_EDiv D i) := by
    rw [← haddA, hkl, haddB]
    exact mul_comm _ _
  -- Cross-multiply to get the quotient identity.
  rw [divPt, div_eq_div_iff_mul_eq_mul]
  exact key

end

end Work.Universal
