/-
Area AV: the scaled `𝔾_m`-action on `ℙ¹` — the orbit map `𝔾_m ⟶ ℙ¹` and the fixed point `∞`.
-/
import Mathlib
import Submission.Work.AbVar.P1Action.SourceChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MvPolynomial HomogeneousLocalization Limits
open scoped MonoidalCategory TensorProduct

namespace Work.AbVar.P1Action

section

variable (k : Type*) [Field k]

/-- Evaluation of the chart coordinate `X₀/X₁` of `D₊(X₁)` at `T ∈ 𝔾_m`. -/
noncomputable def chartEvalT : chartRing k 1 →+* L k :=
  (Polynomial.aeval (LaurentPolynomial.T 1)).toRingHom.comp
    (Work.AbVar.ProjectiveLine.awayToPoly (R := k) 1)

lemma chartEvalT_algebraMap (c : k) :
    chartEvalT k (algebraMap k (chartRing k 1) c) = algebraMap k (L k) c := by
  rw [chartEvalT, RingHom.comp_apply, Work.AbVar.ProjectiveLine.awayToPoly_algMap]
  change (Polynomial.aeval (LaurentPolynomial.T 1)) (Polynomial.C c) = _
  rw [Polynomial.aeval_C]

/-- `chartEvalT k` as a `k`-algebra homomorphism `Away 𝒜 (X₁) →ₐ[k] k[T;T⁻¹]`. -/
noncomputable def chartEvalTAlgHom : chartRing k 1 →ₐ[k] L k where
  toRingHom := chartEvalT k
  commutes' := chartEvalT_algebraMap k

@[simp] lemma chartEvalTAlgHom_apply (x : chartRing k 1) :
    chartEvalTAlgHom k x = chartEvalT k x := rfl

lemma chartEvalTAlgHom_toRingHom :
    (chartEvalTAlgHom k).toRingHom = chartEvalT k := rfl

/-- `chartEvalT` composed with `polyToAway` is `aeval T`. -/
lemma chartEvalT_polyToAway (p : Polynomial k) :
    chartEvalT k (Work.AbVar.ProjectiveLine.polyToAway (R := k) 1 0 p)
      = Polynomial.aeval (LaurentPolynomial.T 1) p := by
  rw [chartEvalT, RingHom.comp_apply,
    Work.AbVar.ProjectiveLine.awayToPoly_polyToAway (R := k) (i := 1) (j := 0) (by decide)]
  rfl

/-- The value of `chartEvalT` on the standard generator `X₀/X₁`. -/
lemma chartEvalT_awayU :
    chartEvalT k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0) = LaurentPolynomial.T 1 := by
  rw [← Work.AbVar.ProjectiveLine.polyToAway_X (R := k) (i := 1) (j := 0), chartEvalT_polyToAway]
  exact Polynomial.aeval_X _

/-- The open immersion `𝔾_m ⟶ ℙ¹`, `T ↦ [T : 1]`. -/
noncomputable def gmToP1 : Work.AbVar.Gm k ⟶ Work.AbVar.P1 k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (chartEvalT k)) ≫ chartObjHom k 1) (by
    have hgen : (Spec.map (CommRingCat.ofHom (chartEvalT k)) ≫ chartObjHom k 1)
        ≫ (Work.AbVar.P1 k).hom = gmHom k := by
      rw [Category.assoc, chartObjHom_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext c
      rw [RingHom.comp_apply, chartEvalT_algebraMap]
    exact hgen)

/-- Evaluation of the chart coordinate `X₁/X₀` of `D₊(X₀)` at `0`; the point `∞ = [1 : 0]`. -/
noncomputable def chartEvalZero : chartRing k 0 →+* k :=
  (Polynomial.eval₂RingHom (RingHom.id k) 0).comp (Work.AbVar.ProjectiveLine.awayToPoly (R := k) 0)

lemma chartEvalZero_algebraMap (c : k) :
    chartEvalZero k (algebraMap k (chartRing k 0) c) = c := by
  rw [chartEvalZero, RingHom.comp_apply, Work.AbVar.ProjectiveLine.awayToPoly_algMap]
  change Polynomial.eval₂ (RingHom.id k) 0 (Polynomial.C c) = c
  rw [Polynomial.eval₂_C, RingHom.id_apply]

/-- `chartEvalZero k` as a `k`-algebra homomorphism `Away 𝒜 (X₀) →ₐ[k] k`. -/
noncomputable def chartEvalZeroAlgHom : chartRing k 0 →ₐ[k] k where
  toRingHom := chartEvalZero k
  commutes' := chartEvalZero_algebraMap k

@[simp] lemma chartEvalZeroAlgHom_apply (x : chartRing k 0) :
    chartEvalZeroAlgHom k x = chartEvalZero k x := rfl

lemma chartEvalZeroAlgHom_toRingHom :
    (chartEvalZeroAlgHom k).toRingHom = chartEvalZero k := rfl

/-- `chartEvalZero` composed with `polyToAway` is evaluation at zero. -/
lemma chartEvalZero_polyToAway (p : Polynomial k) :
    chartEvalZero k (Work.AbVar.ProjectiveLine.polyToAway (R := k) 0 1 p)
      = Polynomial.eval₂ (RingHom.id k) 0 p := by
  rw [chartEvalZero, RingHom.comp_apply,
    Work.AbVar.ProjectiveLine.awayToPoly_polyToAway (R := k) (i := 0) (j := 1) (by decide)]
  rfl

/-- The value of `chartEvalZero` on the standard generator `X₁/X₀`. -/
lemma chartEvalZero_awayU :
    chartEvalZero k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1) = 0 := by
  rw [← Work.AbVar.ProjectiveLine.polyToAway_X (R := k) (i := 0) (j := 1),
    chartEvalZero_polyToAway]
  exact Polynomial.eval₂_X _ _

/-- The point `∞ = [1 : 0]` of `ℙ¹`. -/
noncomputable def pointInf : Work.AbVar.Point (Work.AbVar.P1 k) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (chartEvalZero k)) ≫ chartObjHom k 0) (by
    have hgen : (Spec.map (CommRingCat.ofHom (chartEvalZero k)) ≫ chartObjHom k 0)
        ≫ (Work.AbVar.P1 k).hom = 𝟙 (Spec (.of k)) := by
      rw [Category.assoc, chartObjHom_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [show ((chartEvalZero k).comp (algebraMap k (chartRing k 0))) = RingHom.id k from
        RingHom.ext fun c => chartEvalZero_algebraMap k c]
      exact Spec.map_id _
    exact hgen)

end

end Work.AbVar.P1Action
