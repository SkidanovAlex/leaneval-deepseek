import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Flows of vector fields on manifolds: definitions and the model-space Picard–Lindelöf flow

This file sets up the vocabulary for the global flow theorem
`Work.Morse.continuous_flow`:

* `chartVF v x₀` — the vector field `v` written in the chart at `x₀`;
* `IsFlowBox v ε U Ψ` — the statement that `Ψ` is a local flow box of `v` on the time interval
  `Ioo (-ε) ε` and the set `U`: `Ψ` is jointly continuous there and for every `x ∈ U` the curve
  `t ↦ Ψ t x` is an integral curve of `v` with `Ψ 0 x = x`;
* `ODE_flow_mem` — the Picard–Lindelöf theorem in the form of a *jointly continuous* local flow
  whose solutions stay in a prescribed ball;
* `exists_flow_model` — the same, starting from `ContDiffAt ℝ 1` of the vector field.
-/

open scoped Manifold ContDiff Topology
open Set Function Metric

namespace Work.Morse

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The vector field `v` written in the chart at `x₀`: for `y` in the chart target, this is the
coordinate expression of `v` at the point of `M` with coordinates `y`, in the coordinates of the
chart at `x₀` itself. -/
noncomputable def chartVF (v : (x : M) → TangentSpace (𝓡 n) x) (x₀ : M) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y ↦ tangentCoordChange (𝓡 n) ((extChartAt (𝓡 n) x₀).symm y) x₀
    ((extChartAt (𝓡 n) x₀).symm y) (v ((extChartAt (𝓡 n) x₀).symm y))

/-- `IsFlowBox v ε U Ψ` says that `Ψ` is a local flow box of the vector field `v` on the time
interval `Ioo (-ε) ε` and the set `U`: `Ψ` is jointly continuous on `Ioo (-ε) ε × U`, and for every
`x ∈ U` the curve `t ↦ Ψ t x` is an integral curve of `v` on `Ioo (-ε) ε` with `Ψ 0 x = x`.

The values of `Ψ` outside of `Ioo (-ε) ε × U` are junk. -/
def IsFlowBox (v : (x : M) → TangentSpace (𝓡 n) x) (ε : ℝ) (U : Set M) (Ψ : ℝ → M → M) : Prop :=
  ContinuousOn (uncurry Ψ) (Ioo (-ε) ε ×ˢ U) ∧
    ∀ x ∈ U, Ψ 0 x = x ∧ IsMIntegralCurveOn (fun t ↦ Ψ t x) v (Ioo (-ε) ε)

/-- Picard–Lindelöf, in the form of a jointly continuous local flow. Besides the usual conclusions
(the flow is a solution of the ODE for every initial point in the ball `Metric.closedBall x₀ r`, and it is
continuous on `Metric.closedBall x₀ r ×ˢ Icc tmin tmax`), the solutions are shown to remain in the ball
`Metric.closedBall x₀ a` on which the assumptions on the vector field are made. -/
theorem ODE_flow_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : NNReal}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E × ℝ → E,
      (∀ x ∈ Metric.closedBall x₀ (r : ℝ), α ⟨x, t₀⟩ = x ∧
        ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) (Icc tmin tmax) t ∧
          α ⟨x, t⟩ ∈ Metric.closedBall x₀ (a : ℝ)) ∧
      ContinuousOn α (Metric.closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax) := by
  classical
  have hfix (x : E) (hx : x ∈ Metric.closedBall x₀ (r : ℝ)) := ODE.FunSpace.exists_isFixedPt_next hf hx
  choose α hα using hfix
  set α' : E → ℝ → E := fun (x : E) ↦
    if hx : x ∈ Metric.closedBall x₀ (r : ℝ) then (α x hx).compProj else 0 with hα'
  have hα'eq : ∀ (x : E) (hx : x ∈ Metric.closedBall x₀ (r : ℝ)), α' x = (α x hx).compProj := by
    intro x hx
    rw [hα']
    exact dif_pos hx
  have hderiv : ∀ x ∈ Metric.closedBall x₀ (r : ℝ), ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (α' x) (f t (α' x t)) (Icc tmin tmax) t := by
    intro x hx t ht
    rw [hα'eq x hx]
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      (α x hx).continuous_compProj.continuousOn
      (fun _ ht' ↦ (α x hx).compProj_mem_closedBall hf.mul_max_le) x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα x hx]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  have hinit : ∀ x ∈ Metric.closedBall x₀ (r : ℝ), α' x t₀ = x := by
    intro x hx
    rw [hα'eq x hx, ODE.FunSpace.compProj_val, ← hα x hx]
    exact ODE.FunSpace.next_apply₀ hf hx (α x hx)
  have hmem : ∀ x ∈ Metric.closedBall x₀ (r : ℝ), ∀ t ∈ Icc tmin tmax,
      α' x t ∈ Metric.closedBall x₀ (a : ℝ) := by
    intro x hx t ht
    rw [hα'eq x hx]
    exact (α x hx).mem_closedBall hf.mul_max_le
  have hcont : ContinuousOn (uncurry α') (Metric.closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax) := by
    obtain ⟨L', hL'⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    have hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α' · t) (Metric.closedBall x₀ (r : ℝ)) := by
      intro t ht
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
      rw [hα'eq x hx, hα'eq y hy, ODE.FunSpace.compProj_apply, ODE.FunSpace.compProj_apply,
        ← ODE.FunSpace.toContinuousMap_apply_eq_apply, ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
      have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
      apply ContinuousMap.dist_le_iff_of_nonempty.mp
      exact hL' x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hlip
    intro x hx
    exact fun t ht ↦ (hderiv x hx t ht).continuousWithinAt
  exact ⟨uncurry α', fun x hx ↦ ⟨hinit x hx, fun t ht ↦ ⟨hderiv x hx t ht, hmem x hx t ht⟩⟩,
    hcont⟩

/-- **Model-space local flow.** If `g : E → E` is `C¹` at `c` and `0 < ρ`, then there are
`0 < a ≤ ρ`, `0 < r ≤ ρ`, `0 < ε ≤ ρ` and a map `α : E × ℝ → E` such that

* `α` is continuous on `Metric.closedBall c r ×ˢ Icc (-ε) ε`;
* for every `x ∈ Metric.closedBall c r`, `α x 0 = x` and `t ↦ α x t` solves `y' = g y` on `(-ε, ε)`, and
  moreover stays in the ball `Metric.closedBall c a`. -/
theorem exists_flow_model {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : E → E} {c : E} (hg : ContDiffAt ℝ 1 g c) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (a r ε : ℝ) (α : E × ℝ → E),
      0 < a ∧ a ≤ ρ ∧ 0 < r ∧ r ≤ ρ ∧ 0 < ε ∧ ε ≤ ρ ∧
      ContinuousOn α (Metric.closedBall c r ×ˢ Icc (-ε) ε) ∧
      (∀ x ∈ Metric.closedBall c r,
        α ⟨x, 0⟩ = x ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (α ⟨x, ·⟩) (g (α ⟨x, t⟩)) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, α ⟨x, t⟩ ∈ Metric.closedBall c a)) := by
  obtain ⟨K, s, hs, hls⟩ := hg.exists_lipschitzOnWith
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  have hc_mem : c ∈ s := mem_of_mem_nhds hs
  have hmin : 0 < min δ ρ := lt_min hδ hρ
  set a : ℝ := min δ ρ / 2 with ha
  have ha0 : 0 < a := by positivity
  have haρ : a ≤ ρ := by
    have : min δ ρ ≤ ρ := min_le_right _ _
    simp only [ha]; linarith
  have has : Metric.closedBall c a ⊆ s := by
    intro y hy
    apply hδs
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    simp only [ha] at hy ⊢
    linarith [min_le_left δ ρ]
  have hls' : LipschitzOnWith K g (Metric.closedBall c a) := hls.mono has
  set L : ℝ := K * a + ‖g c‖ + 1 with hL
  have hL0 : 0 < L := by
    rw [hL]
    have h1 : (0 : ℝ) ≤ ↑K * a := mul_nonneg K.coe_nonneg ha0.le
    have h2 : (0 : ℝ) ≤ ‖g c‖ := norm_nonneg _
    linarith
  have hLge1 : (1 : ℝ) ≤ L := by
    rw [hL]
    have h1 : (0 : ℝ) ≤ ↑K * a := mul_nonneg K.coe_nonneg ha0.le
    have h2 : (0 : ℝ) ≤ ‖g c‖ := norm_nonneg _
    linarith
  have hbnd : ∀ y ∈ Metric.closedBall c a, ‖g y‖ ≤ L := by
    intro y hy
    calc ‖g y‖ ≤ ‖g y - g c‖ + ‖g c‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖y - c‖ + ‖g c‖ := by
        gcongr
        have h := hls'.dist_le_mul y hy c (Metric.mem_closedBall_self ha0.le)
        simpa only [dist_eq_norm] using h
      _ ≤ K * a + ‖g c‖ := by
        gcongr
        rwa [mem_closedBall_iff_norm] at hy
      _ ≤ L := by simp only [hL]; linarith
  set r : ℝ := a / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrρ : r ≤ ρ := by simp only [hr]; linarith
  set ε : ℝ := a / (2 * L) with hε
  have hε0 : 0 < ε := by positivity
  have hερ : ε ≤ ρ := by
    have h2L : (1 : ℝ) ≤ 2 * L := by linarith
    have h1 : ε ≤ a := by
      rw [hε, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * L)]
      nlinarith
    linarith [haρ]
  have hmul : L * ε ≤ a - r := by
    have hLx : L * ε = a / 2 := by
      rw [hε, mul_div_assoc', mul_comm 2 L]
      exact mul_div_mul_left a 2 (ne_of_gt hL0)
    rw [hLx, hr]
    linarith
  have hPL : IsPicardLindelof (fun _ : ℝ ↦ g) (tmin := -ε) (tmax := ε)
      ⟨0, by constructor <;> linarith⟩ c ⟨a, ha0.le⟩ ⟨r, hr0.le⟩ ⟨L, hL0.le⟩ K := by
    apply IsPicardLindelof.of_time_independent hbnd hls'
    simp only [sub_zero, zero_sub, neg_neg, max_self]
    exact hmul
  obtain ⟨α, hα, hcont⟩ := ODE_flow_mem hPL
  refine ⟨a, r, ε, α, ha0, haρ, hr0, hrρ, hε0, hερ, hcont, fun x hx ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hα x hx
  exact ⟨h1, fun t ht ↦ (h2 t ht).1, fun t ht ↦ (h2 t ht).2⟩

end Work.Morse
