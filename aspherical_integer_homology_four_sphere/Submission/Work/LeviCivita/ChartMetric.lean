/-
# The chart metric as a continuous bilinear form, and its smoothness in chart coordinates

`Submission.ChartConnection.chartGram x₀ p a b = ⟪frameVector x₀ p a, frameVector x₀ p b⟫` is the
Riemannian metric of `M` read in the chart at `x₀`, as a bilinear form on the coordinate vectors
`a b : E`.

This file packages that bilinear form as a continuous linear map
`chartGramCLM x₀ p : E →L[ℝ] E →L[ℝ] ℝ`, records its positive definiteness, and states the key
analytic input of area LC: **the chart metric is smooth in the chart coordinates**, i.e. for `p` in
the source of the chart at `x₀` the function

    q ↦ chartGramCLM x₀ ((extChartAt I x₀).symm q)

is `C^∞` at `extChartAt I x₀ p`.

The smoothness is proved from the framework hypothesis `IsContMDiffRiemannianBundle I ∞ E _`
together with the smoothness of the chart frame sections
(`Submission.Geodesic.contMDiffAt_frameSection`) and the smoothness of the inner product of two
smooth sections (`ContMDiff.inner_bundle`).
-/
import Submission.Work.LeviCivita.Defs
import Submission.Work.RiemLib.ChartConnection

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSectionVars false
set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.ChartConnection
open Submission.Geodesic

namespace Work.LeviCivita

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-! ## The chart metric as a continuous bilinear form -/

/-- The chart metric of `x₀` at `p`, as a `ℝ`-bilinear form on coordinate vectors. -/
noncomputable def chartGramBilin (x₀ p : M) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun a :=
    { toFun := fun b ↦ chartGram (I := I) x₀ p a b
      map_add' := fun b₁ b₂ ↦ chartGram_add_snd (I := I) x₀ p a b₁ b₂
      map_smul' := fun c b ↦ chartGram_smul_snd (I := I) x₀ p c a b }
  map_add' a₁ a₂ := by
    ext b
    exact chartGram_add_fst (I := I) x₀ p a₁ a₂ b
  map_smul' c a := by
    ext b
    exact chartGram_smul_fst (I := I) x₀ p c a b

section normbound

variable {x₀ p : M}

/-- The frame map `v ↦ frameVector x₀ p v` is the continuous linear map `symmL` of the tangent
trivialisation. -/
lemma chartGram_norm_bound (a b : E) :
    ‖chartGram (I := I) x₀ p a b‖
      ≤ ‖(trivializationAt E (TangentSpace I) x₀).symmL ℝ p‖ ^ 2 * ‖a‖ * ‖b‖ := by
  set C : ℝ := ‖(trivializationAt E (TangentSpace I) x₀).symmL ℝ p‖ with hC
  have h2 : ‖frameVector (I := I) x₀ p a‖ ≤ C * ‖a‖ := by
    rw [hC, frameVector]
    exact ContinuousLinearMap.le_opNorm _ _
  have h3 : ‖frameVector (I := I) x₀ p b‖ ≤ C * ‖b‖ := by
    rw [hC, frameVector]
    exact ContinuousLinearMap.le_opNorm _ _
  calc ‖chartGram (I := I) x₀ p a b‖
      = |inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b)| := by
        rw [chartGram_apply, Real.norm_eq_abs]
    _ ≤ ‖frameVector (I := I) x₀ p a‖ * ‖frameVector (I := I) x₀ p b‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ (C * ‖a‖) * (C * ‖b‖) := by
        exact mul_le_mul h2 h3 (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))
    _ = C ^ 2 * ‖a‖ * ‖b‖ := by ring

end normbound

/-- **The chart metric as a continuous bilinear form.** -/
noncomputable def chartGramCLM (x₀ p : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (chartGramBilin (I := I) x₀ p)
    (‖(trivializationAt E (TangentSpace I) x₀).symmL ℝ p‖ ^ 2)
    (fun a b ↦ chartGram_norm_bound (I := I) (x₀ := x₀) (p := p) a b)

@[simp] lemma chartGramCLM_apply (x₀ p : M) (a b : E) :
    chartGramCLM (I := I) x₀ p a b = chartGram (I := I) x₀ p a b := rfl

/-- The chart metric is positive definite on the chart source. -/
lemma chartGram_posDef (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) {v : E} (hv : v ≠ 0) :
    0 < chartGramCLM (I := I) x₀ p v v := by
  rw [chartGramCLM_apply, chartGram_apply]
  have hbase : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hp
  have hne : frameVector (I := I) x₀ p v ≠ 0 := by
    intro h
    apply hv
    have h1 : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
        (frameVector (I := I) x₀ p v) = 0 := by rw [h, map_zero]
    rw [frameVector, Trivialization.continuousLinearMapAt_symmL _ hbase] at h1
    exact h1
  exact real_inner_self_pos.mpr hne

/-- **Nondegeneracy of the chart metric**: it separates coordinate vectors. -/
lemma chartGram_left_separating (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) {v v' : E}
    (h : ∀ w, chartGram (I := I) x₀ p v w = chartGram (I := I) x₀ p v' w) : v = v' := by
  have hzero : ∀ w, chartGram (I := I) x₀ p (v - v') w = 0 := by
    intro w
    rw [sub_eq_add_neg, ← neg_one_smul ℝ v', chartGram_add_fst, chartGram_smul_fst, h w]
    ring
  rcases eq_or_ne (v - v') 0 with hz | hz
  · exact sub_eq_zero.mp hz
  · have hpos := chartGram_posDef (I := I) (x₀ := x₀) (p := p) hp hz
    rw [chartGramCLM_apply, hzero (v - v')] at hpos
    exact absurd hpos (lt_irrefl 0)

end

end Work.LeviCivita
