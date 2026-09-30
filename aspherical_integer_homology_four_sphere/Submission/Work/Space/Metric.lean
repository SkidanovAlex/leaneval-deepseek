/-
# The Riemannian metric of a space with a finite atlas of isometric models

This file is the third layer of the area `Space/`: the Riemannian metric `gM` of `M̂`, built from
the **chart models** of blueprint §1 (the upper half space metric, the warped filling metric, the
flat core metric).

## The data

`ModelAtlas M` extends the finite atlas `Work.Space.FinAtlas` by a metric model per chart:

* `model i : E4 → E4 →L[ℝ] E4 →L[ℝ] ℝ` — a smooth family of inner products on `E4`;
* `model_smooth`, `model_symm`, `model_pos` — smoothness, symmetry, positive definiteness.

The remaining input, **that the transitions between the charts are isometries of the models**, is a
hypothesis of the theorems rather than a field, because its statement needs the tangent bundle
(`ChartedSpace`/`IsManifold`); it is `Work.Space.ModelAtlas.Isometry`:

  `∀ x, ∀ᶠ y in 𝓝 x, ∀ a b, model_{i(y)}(chart_{i(y)} y) (tangentCoordChange I4 x y y a)
      (tangentCoordChange I4 x y y b) = model_{i(x)}(chart_{i(x)} y) a b`.

It is automatic where the priority index is locally constant, and on the overlap of two charts it is
the geometric statement that the transition is an isometry of the two models (a Möbius map for the
hyperbolic charts, `(r,s) ↦ (logarithm, exponential)` for the polar charts).

## Main definitions and results

* `Work.Space.ModelAtlas.gM` — the family of inner products
  `gM.inner y = model (indexOf y) (chartAt y y)`.
* `Work.Space.ModelAtlas.instRiemannianBundle` — the `RiemannianBundle` instance.
* `Work.Space.ModelAtlas.inner_eq` — `inner ℝ v w = model (indexOf y) (chartAt y y) v w`.
* `Work.Space.ModelAtlas.Isometry` — the isometry hypothesis on the transitions.
-/
import Mathlib
import Submission.Work.Space.Atlas
import Submission.Work.Curvature.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Manifold ContDiff Topology Bundle
open Bundle

namespace Work.Space

/-- **A finite atlas with metric models.**  Each chart `i` comes with a metric field `model i` on
`E4`; the models are smooth, symmetric and positive definite. -/
class ModelAtlas (M : Type*) [TopologicalSpace M] extends FinAtlas M where
  /-- The metric model attached to each chart. -/
  model : Fin n → E4 → (E4 →L[ℝ] E4 →L[ℝ] ℝ)
  /-- The models are smooth families of bilinear forms. -/
  model_smooth : ∀ i, ContMDiff 𝓘(ℝ, E4)
    (𝓘(ℝ, E4).prod 𝓘(ℝ, E4 →L[ℝ] E4 →L[ℝ] ℝ)) ∞
    (fun q : E4 => TotalSpace.mk' (E4 →L[ℝ] E4 →L[ℝ] ℝ) q (model i q))
  /-- The models are symmetric. -/
  model_symm : ∀ i (q v w : E4), model i q v w = model i q w v
  /-- The models are positive definite. -/
  model_pos : ∀ i (q : E4) (v : E4), v ≠ 0 → 0 < model i q v v

/-- A point of the unit sphere of `E4` is nonzero. -/
theorem ne_zero_of_mem_sphere {v : E4} (hv : v ∈ Metric.sphere (0 : E4) 1) : v ≠ 0 := by
  intro h; rw [h] at hv; simp at hv

/-- **A positive definite continuous bilinear form on `E4` is bounded below by a multiple of the
square of the norm.** -/
theorem exists_pos_le_self_of_posDef (G : E4 →L[ℝ] E4 →L[ℝ] ℝ)
    (hG : ∀ v : E4, v ≠ 0 → 0 < G v v) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v : E4, lam * ‖v‖ ^ 2 ≤ G v v := by
  have hcont : Continuous fun v : E4 => G v v := G.continuous.clm_apply continuous_id
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : E4) 1).exists_isMinOn
    (by simp) hcont.continuousOn
  have hv₀ne : v₀ ≠ 0 := ne_zero_of_mem_sphere hv₀
  refine ⟨G v₀ v₀, hG v₀ hv₀ne, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  · have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hsp : (‖v‖⁻¹) • v ∈ Metric.sphere (0 : E4) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ hnorm]
    have h1 : G v₀ v₀ ≤ G ((‖v‖⁻¹) • v) ((‖v‖⁻¹) • v) := hmin hsp
    have hsm : ∀ c : ℝ, G (c • v) (c • v) = c * (c * G v v) := by
      intro c
      rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
        ContinuousLinearMap.smul_apply]
      ring
    rw [hsm] at h1
    have h4 : (‖v‖⁻¹) * ((‖v‖⁻¹) * G v v) = G v v / ‖v‖ ^ 2 := by
      field_simp
    rw [h4] at h1
    have hpos : 0 < ‖v‖ ^ 2 := by positivity
    rw [le_div_iff₀ hpos] at h1
    linarith

/-- **The unit ball of a positive definite bilinear form on `E4` is von Neumann bounded.** -/
theorem isVonNBounded_of_posDef (G : E4 →L[ℝ] E4 →L[ℝ] ℝ)
    (hG : ∀ v : E4, v ≠ 0 → 0 < G v v) :
    Bornology.IsVonNBounded ℝ {v : E4 | G v v < 1} := by
  obtain ⟨lam, hlam, hbound⟩ := exists_pos_le_self_of_posDef G hG
  refine (NormedSpace.isVonNBounded_of_isBounded ℝ
    (Metric.isBounded_closedBall (x := (0 : E4))
      (r := Real.sqrt (1/lam) + 1))).subset ?_
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : lam * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hbound v) hv
  have hsq : ‖v‖ ^ 2 < 1/lam := by
    rw [lt_div_iff₀ hlam]
    linarith [h1]
  have h3 : ‖v‖ < Real.sqrt (1/lam) := by
    rw [← Real.sqrt_sq (norm_nonneg v)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hsq
  linarith

namespace ModelAtlas

variable {M : Type*} [TopologicalSpace M] (A : ModelAtlas M)

/-- The metric field of the `i`-th chart, in the vocabulary of `Curvature`. -/
def field (i : Fin A.n) : Curvature.MetricField := fun q a b => A.model i q a b

/-- The set of model metric fields of the atlas (the `models` of the blueprint). -/
def models : Set Curvature.MetricField := Set.range A.field

theorem field_mem_models (i : Fin A.n) : A.field i ∈ A.models := ⟨i, rfl⟩

/-- **The metric of the model atlas**, as a family of inner products on the tangent spaces: in the
chart of the point `y`, it is the model of that chart. -/
noncomputable def gM [ChartedSpace E4 M] [IsManifold I4 1 M] :
    RiemannianMetric (fun y : M => TangentSpace I4 y) where
  inner y := A.model (A.indexOf y) (chartAt E4 y y)
  symm y v w := A.model_symm _ _ _ _
  pos y v hv := A.model_pos _ _ _ hv
  continuousAt y :=
    ((A.model (A.indexOf y) (chartAt E4 y y)).continuous.continuousAt.clm_apply continuousAt_id)
  isVonNBounded y :=
    isVonNBounded_of_posDef (A.model (A.indexOf y) (chartAt E4 y y))
      (fun v hv => A.model_pos _ _ v hv)

/-- **The Riemannian structure of a model atlas.** -/
instance instRiemannianBundle [A : ModelAtlas M] [ChartedSpace E4 M] [IsManifold I4 1 M] :
    RiemannianBundle (fun y : M => TangentSpace I4 y) :=
  ⟨A.gM⟩

/-- **The inner product in the chart of the point.** -/
theorem inner_eq [ChartedSpace E4 M] [IsManifold I4 1 M] (y : M)
    (v w : TangentSpace I4 y) :
    inner ℝ v w = A.model (A.indexOf y) (chartAt E4 y y) v w := rfl

end ModelAtlas

/-- **The isometry hypothesis**: the transitions between the charts of the model atlas are
isometries of the models. -/
def ModelAtlas.Isometry {M : Type*} [TopologicalSpace M] (A : ModelAtlas M)
    [ChartedSpace E4 M] [IsManifold I4 1 M] : Prop :=
  ∀ x : M, ∀ᶠ y in 𝓝 x, ∀ a b : E4,
    A.model (A.indexOf y) (chartAt E4 y y) (tangentCoordChange I4 x y y a)
        (tangentCoordChange I4 x y y b)
      = A.model (A.indexOf x) (chartAt E4 x y) a b

/-- The isometry hypothesis, as a **class**: this is what the instances
`Work.Space.ModelAtlas.instIsContMDiffRiemannianBundle` of `Work.Space.MetricBundle` look for. -/
class ModelAtlas.HasIsometry {M : Type*} [TopologicalSpace M] (A : ModelAtlas M)
    [ChartedSpace E4 M] [IsManifold I4 1 M] : Prop where
  /-- The isometry hypothesis holds. -/
  out : A.Isometry

end Work.Space
