/-
Area AV: the scaled `𝔾_m`-action on `ℙ¹` — the point `∞ = [1:0]` is fixed.

We prove that the graph section `𝔾_m ⟶ ℙ¹ ⊗ 𝔾_m`, `T ↦ (∞, T)`, followed by the scaling
action `scalingAct` equals the constant map `𝔾_m ⟶ ℙ¹` at `∞`.

The computation is made on the affine chart `D₊(X₀)` of `ℙ¹`, which contains `∞`.  The section
`T ↦ (∞, T)` factors through the chart `srcChartι k 0 = D₊(X₀) × 𝔾_m` of the source: the
corresponding ring map is
`psi k : chartRing k 0 ⊗[k] k[T;T⁻¹] → k[T;T⁻¹]`, `a ⊗ t ↦ a(∞) · t`,
which is the unique `k`-algebra map with `psi (a ⊗ 1) = a(∞)` and `psi (1 ⊗ t) = t`.
Composing with the chart description `thetaRing k 0` of the action (which sends `X₁/X₀` to
`(X₁/X₀) ⊗ T⁻¹`) kills the first factor, because `X₁/X₀` vanishes at `∞`.
-/
import Mathlib
import Submission.Work.AbVar.P1Action.Action
import Submission.Work.AbVar.P1Action.Points

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MvPolynomial HomogeneousLocalization Limits
open scoped MonoidalCategory TensorProduct

namespace Work.AbVar.P1Action

section

variable (k : Type*) [Field k]

/-! ## The ring map `psi : chartRing k 0 ⊗[k] k[T;T⁻¹] → k[T;T⁻¹]` of the section at `∞` -/

/-- The `k`-algebra map `chartRing k 0 ⊗[k] k[T;T⁻¹] → k[T;T⁻¹]`, `a ⊗ t ↦ a(∞) · t`. -/
noncomputable abbrev psiAlg : srcChartRing k 0 →ₐ[k] L k :=
  Algebra.TensorProduct.lift ((Algebra.ofId k (L k)).comp (chartEvalZeroAlgHom k))
    (AlgHom.id k (L k))
    (fun x y => Commute.all (((Algebra.ofId k (L k)).comp (chartEvalZeroAlgHom k)) x)
      ((AlgHom.id k (L k)) y))

/-- `psiAlg` regarded as a ring homomorphism. -/
noncomputable abbrev psi : srcChartRing k 0 →+* L k := (psiAlg k).toRingHom

lemma psi_tmul (a : chartRing k 0) (t : L k) :
    psi k (a ⊗ₜ[k] t) = algebraMap k (L k) (chartEvalZero k a) * t := by
  show psiAlg k (a ⊗ₜ[k] t) = _
  rw [psiAlg, Algebra.TensorProduct.lift_tmul]; simp

/-- `psi` restricts to `chartEvalZero` on the first factor. -/
lemma psi_comp_includeLeft :
    (psi k).comp (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := chartRing k 0)
        (B := L k))
      = (algebraMap k (L k)).comp (chartEvalZero k) := by
  apply RingHom.ext; intro a
  rw [RingHom.comp_apply, RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    psi_tmul, _root_.mul_one]

/-- `psi` restricts to the identity on the second factor. -/
lemma psi_comp_includeRight :
    (psi k).comp (↑(Algebra.TensorProduct.includeRight (R := k) (A := chartRing k 0) (B := L k)))
      = RingHom.id (L k) := by
  apply RingHom.ext; intro t
  rw [RingHom.comp_apply, RingHom.id_apply]
  change psi k (Algebra.TensorProduct.includeRight (R := k) (A := chartRing k 0) (B := L k) t) = t
  rw [Algebra.TensorProduct.includeRight_apply, psi_tmul]; simp

/-- The key annihilation: the chart coordinate `X₁/X₀` of `D₊(X₀)` vanishes after the chart
action `thetaRing k 0` and the section map `psi`. -/
lemma psi_comp_thetaRing :
    (psi k).comp (thetaRing k 0) = (algebraMap k (L k)).comp (chartEvalZero k) := by
  refine away_ringHom_ext k (i := 0) (j := 1) (by decide) _ _ ?_ ?_
  · intro c
    rw [RingHom.comp_apply, RingHom.comp_apply, thetaRing_algebraMap]
    change psiAlg k (algebraMap k (srcChartRing k 0) c) = _
    rw [AlgHom.commutes, chartEvalZero_algebraMap]
  · have htheta : thetaRing k 0 (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)
        = Work.AbVar.ProjectiveLine.awayU (R := k) 0 1 ⊗ₜ[k] LaurentPolynomial.T (-1) := by
      have h := thetaRing_awayU k 0
      rw [show other 0 = (1 : Fin 2) from by decide, thetaExp_zero] at h
      exact h
    rw [RingHom.comp_apply, RingHom.comp_apply, htheta, psi_tmul, chartEvalZero_awayU,
      map_zero, zero_mul]

/-! ## The section `T ↦ (∞, T)` lies in the chart `D₊(X₀) × 𝔾_m` -/

lemma specMap_psi_includeLeft :
    Spec.map (CommRingCat.ofHom (psi k))
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := k) (A := chartRing k 0) (B := L k)))
      = Spec.map (CommRingCat.ofHom (algebraMap k (L k)))
          ≫ Spec.map (CommRingCat.ofHom (chartEvalZero k)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, psi_comp_includeLeft,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]

lemma specMap_psi_includeRight :
    Spec.map (CommRingCat.ofHom (psi k))
        ≫ Spec.map (CommRingCat.ofHom (↑(Algebra.TensorProduct.includeRight
            (R := k) (A := chartRing k 0) (B := L k))))
      = 𝟙 (Spec (CommRingCat.of (L k))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, psi_comp_includeRight]
  rw [show CommRingCat.ofHom (RingHom.id (L k)) = 𝟙 (CommRingCat.of (L k)) from rfl]
  exact Spec.map_id _

/-- First projection of the section `T ↦ (∞, T)`. -/
lemma sectionRight_fst_pointInf :
    Over.Hom.left (Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k) (pointInf k))
        ≫ pullback.fst (Work.AbVar.P1 k).hom (gmHom k)
      = Spec.map (CommRingCat.ofHom (algebraMap k (L k)))
          ≫ Spec.map (CommRingCat.ofHom (chartEvalZero k)) ≫ chartObjHom k 0 := by
  change Over.Hom.left (Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k) (pointInf k))
        ≫ pullback.fst (Work.AbVar.P1 k).hom (Work.AbVar.Gm k).hom
      = Spec.map (CommRingCat.ofHom (algebraMap k (L k)))
          ≫ Spec.map (CommRingCat.ofHom (chartEvalZero k)) ≫ chartObjHom k 0
  rw [← Over.fst_left, ← Over.comp_left, Work.AbVar.sectionRight_fst, Over.comp_left,
    Over.toUnit_left]
  rw [gm_hom, gmHom]; rfl

/-- Second projection of the section `T ↦ (∞, T)`. -/
lemma sectionRight_snd_pointInf :
    Over.Hom.left (Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k) (pointInf k))
        ≫ pullback.snd (Work.AbVar.P1 k).hom (gmHom k)
      = 𝟙 (Spec (CommRingCat.of (L k))) := by
  change Over.Hom.left (Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k) (pointInf k))
        ≫ pullback.snd (Work.AbVar.P1 k).hom (Work.AbVar.Gm k).hom
      = 𝟙 (Spec (CommRingCat.of (L k)))
  rw [← Over.snd_left, ← Over.comp_left, Work.AbVar.sectionRight_snd, Over.id_left]; rfl

/-- The section `T ↦ (∞, T)` factors through the chart `srcChartι k 0 = D₊(X₀) × 𝔾_m` of the
source, with chart-coordinate ring map `psi k`. -/
lemma specMap_psi_srcChartι :
    Spec.map (CommRingCat.ofHom (psi k)) ≫ srcChartι k 0
      = Over.Hom.left (Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k)
          (pointInf k)) := by
  apply pullback.hom_ext (f := (Work.AbVar.P1 k).hom) (g := gmHom k)
  · rw [Category.assoc, srcChartι_fst, ← Category.assoc, specMap_psi_includeLeft, Category.assoc]
    exact sectionRight_fst_pointInf k |>.symm
  · rw [Category.assoc, srcChartι_snd, specMap_psi_includeRight]
    exact sectionRight_snd_pointInf k |>.symm

/-! ## The two composites, computed on the chart `D₊(X₀)` -/

/-- The left hand side, computed on the chart `D₊(X₀)`. -/
lemma left_scalingAct :
    Over.Hom.left (Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k) (pointInf k)
        ≫ scalingAct k)
      = Spec.map (CommRingCat.ofHom ((psi k).comp (thetaRing k 0))) ≫ chartObjHom k 0 := by
  have e1 : Over.Hom.left (Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k)
        (pointInf k) ≫ scalingAct k)
      = Over.Hom.left (Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k) (pointInf k))
        ≫ scalingActLeft k := by
    rw [Over.comp_left]; rfl
  have e2 : Over.Hom.left (Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k) (pointInf k))
        ≫ scalingActLeft k
      = (Spec.map (CommRingCat.ofHom (psi k)) ≫ srcChartι k 0) ≫ scalingActLeft k :=
    (congrArg (fun t => t ≫ scalingActLeft k) (specMap_psi_srcChartι k)).symm
  have e3 : (Spec.map (CommRingCat.ofHom (psi k)) ≫ srcChartι k 0) ≫ scalingActLeft k
      = Spec.map (CommRingCat.ofHom ((psi k).comp (thetaRing k 0))) ≫ chartObjHom k 0 := by
    rw [Category.assoc, srcChartι_scalingActLeft, srcChartHom, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact e1.trans (e2.trans e3)

/-- The right hand side, computed on the chart `D₊(X₀)`. -/
lemma right_pointInf :
    Over.Hom.left (SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k) ≫ pointInf k)
      = Spec.map (CommRingCat.ofHom ((algebraMap k (L k)).comp (chartEvalZero k)))
          ≫ chartObjHom k 0 := by
  have e1 : Over.Hom.left (SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k) ≫ pointInf k)
      = (Work.AbVar.Gm k).hom ≫ Over.Hom.left (pointInf k) := by
    rw [Over.comp_left, Over.toUnit_left]
  have e2 : (Work.AbVar.Gm k).hom ≫ Over.Hom.left (pointInf k)
      = Spec.map (CommRingCat.ofHom (algebraMap k (L k)))
        ≫ (Spec.map (CommRingCat.ofHom (chartEvalZero k)) ≫ chartObjHom k 0) := by
    change Spec.map (CommRingCat.ofHom (algebraMap k (L k)))
        ≫ Over.Hom.left (pointInf k) = _
    rw [show Over.Hom.left (pointInf k)
        = Spec.map (CommRingCat.ofHom (chartEvalZero k)) ≫ chartObjHom k 0 from rfl]
  have e3 : Spec.map (CommRingCat.ofHom (algebraMap k (L k)))
        ≫ (Spec.map (CommRingCat.ofHom (chartEvalZero k)) ≫ chartObjHom k 0)
      = Spec.map (CommRingCat.ofHom ((algebraMap k (L k)).comp (chartEvalZero k)))
        ≫ chartObjHom k 0 := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact e1.trans (e2.trans e3)

end

/-- The point `∞ = [1:0]` of `ℙ¹` is fixed by the scaling action. -/
theorem scalingAct_fixed (k : Type*) [Field k] :
    CategoryTheory.CategoryStruct.comp
        (Work.AbVar.sectionRight (Work.AbVar.P1 k) (Work.AbVar.Gm k)
          (Work.AbVar.P1Action.pointInf k))
        (Work.AbVar.P1Action.scalingAct k)
      = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k))
          (Work.AbVar.P1Action.pointInf k) := by
  apply Over.OverMorphism.ext
  have hmid : Spec.map (CommRingCat.ofHom ((psi k).comp (thetaRing k 0))) ≫ chartObjHom k 0
      = Spec.map (CommRingCat.ofHom ((algebraMap k (L k)).comp (chartEvalZero k)))
          ≫ chartObjHom k 0 := by
    rw [psi_comp_thetaRing]
  exact (left_scalingAct k).trans (hmid.trans (right_pointInf k).symm)

end Work.AbVar.P1Action
