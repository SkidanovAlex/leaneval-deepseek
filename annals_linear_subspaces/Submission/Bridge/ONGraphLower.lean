import Mathlib
import Submission.Bridge.ONGraph
import Submission.GeometryOfNumbers.ProjectionDistance

/-!
# Graph residual lower bounds (generic part of paper Lemma 1(a), converse direction)

For an orthonormal family `e` inside a reference plane `x`, graph offsets `c j ∈ xᗮ`,
graph vectors `u j = e j + c j` and the graph subspace `V = span (range u)`, the residual of
the unit graph vector `u i / ‖u i‖ ∈ V` is exactly `‖c i‖ / ‖u i‖`; hence the operator-norm
distance `δ(V,x) = planeResidual V x` dominates each `‖c i‖ / ‖u i‖`, i.e.
`‖c i‖ ≤ ‖u i‖ · δ`.

All results here are Mathlib-only.
-/

noncomputable section

open Module InnerProductGeometry
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.Bridge.ONGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The residual of a graph vector is its offset: `u i − π_x u i = c i`. -/
lemma residual_graphVec {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) (i : Fin k) :
    graphVec e c i - x.starProjection (graphVec e c i) = c i := by
  unfold graphVec
  have h := starProj_graphVec (x := x) e c he_mem hc_orth i
  change x.starProjection (e i + c i) = e i at h
  rw [h]
  abel

/-- Residual of the unit vector `u i / ‖u i‖ ∈ V`: exactly `‖c i‖ / ‖u i‖`. -/
lemma unit_graphVec_residual {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) (i : Fin k) :
    ‖((1 / ‖graphVec e c i‖) • graphVec e c i) -
        ((x.orthogonalProjectionOnto ((1 / ‖graphVec e c i‖) • graphVec e c i)) : E)‖ =
      ‖c i‖ / ‖graphVec e c i‖ := by
  let u : E := graphVec e c i
  have hpos : 0 < ‖u‖ := by
    exact norm_pos_iff.mpr (graphVec_ne_zero (x := x) e c he he_mem hc_orth i)
  have hres : u - x.starProjection u = c i := by
    dsimp [u]
    exact residual_graphVec (x := x) e c he_mem hc_orth i
  calc
    ‖((1 / ‖u‖) • u) - ((x.orthogonalProjectionOnto ((1 / ‖u‖) • u)) : E)‖
        = ‖((1 / ‖u‖) • u) - x.starProjection ((1 / ‖u‖) • u)‖ := by simp
    _ = ‖(1 / ‖u‖) • (u - x.starProjection u)‖ := by
          simp [smul_sub, map_smul]
    _ = ‖(1 / ‖u‖) • c i‖ := by rw [hres]
    _ = (1 / ‖u‖) * ‖c i‖ := by
          rw [norm_smul]
          have hnn : 0 ≤ (1 / ‖u‖) := by positivity
          simp [Real.norm_eq_abs, abs_of_nonneg hnn]
    _ = ‖c i‖ / ‖u‖ := by field_simp
    _ = ‖c i‖ / ‖graphVec e c i‖ := rfl

/-- The residual set of `planeResidual` is bounded above by 1. -/
lemma residualSet_bddAbove (V x : Submodule ℝ E) :
    BddAbove {r : ℝ | ∃ v : E, v ∈ V ∧ ‖v‖ = 1 ∧
      ‖v - ((x.orthogonalProjectionOnto v) : E)‖ = r} := by
  refine ⟨1, ?_⟩
  intro r hr
  rcases hr with ⟨v, hvV, hv1, rfl⟩
  calc
    ‖v - ((x.orthogonalProjectionOnto v) : E)‖ = ‖(xᗮ).starProjection v‖ := by simp
    _ = ‖((xᗮ).orthogonalProjectionOnto v : E)‖ := by simp
    _ ≤ ‖v‖ := Submodule.norm_orthogonalProjectionOnto_apply_le (xᗮ) v
    _ = 1 := hv1

/-- The operator-norm distance `δ(V,x)` dominates each single `‖c i‖ / ‖u i‖`. -/
lemma planeResidual_ge_unit_graphVec {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) (i : Fin k) :
    ‖c i‖ / ‖graphVec e c i‖ ≤
      Submission.ProjectionDistance.planeResidual (graphSubspace e c) x := by
  classical
  let S : Set ℝ := {r : ℝ | ∃ v : E,
    v ∈ graphSubspace e c ∧ ‖v‖ = 1 ∧
      ‖v - ((x.orthogonalProjectionOnto v) : E)‖ = r}
  have hS : Submission.ProjectionDistance.planeResidual (graphSubspace e c) x = sSup S := rfl
  have hbdd : BddAbove S := residualSet_bddAbove (graphSubspace e c) x
  let u : E := graphVec e c i
  have hpos : 0 < ‖u‖ := by
    exact norm_pos_iff.mpr (graphVec_ne_zero (x := x) e c he he_mem hc_orth i)
  have hres : ‖((1 / ‖u‖) • u) - ((x.orthogonalProjectionOnto ((1 / ‖u‖) • u)) : E)‖ =
      ‖c i‖ / ‖u‖ := by
    dsimp [u]
    exact unit_graphVec_residual (x := x) e c he he_mem hc_orth i
  have hmem : ‖c i‖ / ‖graphVec e c i‖ ∈ S := by
    refine ⟨(1 / ‖u‖) • u, ?_, ?_, ?_⟩
    · have hu0 : u ∈ graphSubspace e c := by
        refine Submodule.subset_span ?_
        exact Set.mem_range.mpr ⟨i, rfl⟩
      exact Submodule.smul_mem _ _ hu0
    · simp [norm_smul, abs_of_pos (one_div_pos.mpr hpos), hpos.ne']
    · dsimp [u] at hres ⊢
      exact hres
  exact (le_csSup hbdd hmem).trans_eq hS

/-- `‖c i‖ ≤ ‖u i‖ · δ(V,x)` for every index `i`. -/
lemma planeResidual_ge_norm_c {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) (i : Fin k) :
    ‖c i‖ ≤ ‖graphVec e c i‖ *
      Submission.ProjectionDistance.planeResidual (graphSubspace e c) x := by
  have hge := planeResidual_ge_unit_graphVec (x := x) e c he he_mem hc_orth i
  have hpos : 0 < ‖graphVec e c i‖ := by
    exact norm_pos_iff.mpr (graphVec_ne_zero (x := x) e c he he_mem hc_orth i)
  rw [div_le_iff₀ hpos] at hge
  rwa [mul_comm] at hge


/-- `‖u i‖ ≤ 1 + ‖c i‖` for a graph vector (`‖u i‖² = 1 + ‖c i‖² ≤ (1 + ‖c i‖)²`). -/
lemma graphVec_norm_le_one_add {x : Submodule ℝ E} {k : ℕ} (e c : Fin k → E)
    (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x) (hc_orth : ∀ j, c j ∈ xᗮ) (i : Fin k) :
    ‖graphVec e c i‖ ≤ 1 + ‖c i‖ := by
  have hsq := graphVec_normSq (x := x) e c he he_mem hc_orth i
  have hsq2 : ‖graphVec e c i‖ ^ 2 ≤ (1 + ‖c i‖) ^ 2 := by
    rw [hsq]
    nlinarith [norm_nonneg (c i)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq2

/-- **Lemma 1(a), offset bound**: for a graph with `δ = planeResidual V x ≤ 1/2`, every
offset satisfies `‖c i‖ ≤ 2·δ`.  (From `δ ≥ ‖c i‖/‖u i‖` and `‖u i‖ ≤ 1 + ‖c i‖` one gets
`‖c i‖ ≤ δ·(1 + ‖c i‖)`, hence `‖c i‖ ≤ δ/(1−δ) ≤ 2δ`.) -/
lemma graph_residual_le_two_planeResidual {x : Submodule ℝ E} {k : ℕ} (hk : 0 < k)
    (e c : Fin k → E) (he : Orthonormal ℝ e) (he_mem : ∀ j, e j ∈ x)
    (hc_orth : ∀ j, c j ∈ xᗮ) (i : Fin k)
    (hδ12 : Submission.ProjectionDistance.planeResidual (graphSubspace e c) x ≤ 1 / 2) :
    ‖c i‖ ≤ 2 * Submission.ProjectionDistance.planeResidual (graphSubspace e c) x := by
  classical
  let δ : ℝ := Submission.ProjectionDistance.planeResidual (graphSubspace e c) x
  let u : E := graphVec e c i
  have hpos : 0 < ‖u‖ := by
    exact norm_pos_iff.mpr (graphVec_ne_zero (x := x) e c he he_mem hc_orth i)
  have hd0 : 0 ≤ δ := by
    have hdivle : ‖c i‖ / ‖graphVec e c i‖ ≤ δ := by
      have hg := planeResidual_ge_unit_graphVec (x := x) e c he he_mem hc_orth i
      simpa [δ] using hg
    have hdiv0 : 0 ≤ ‖c i‖ / ‖graphVec e c i‖ := div_nonneg (norm_nonneg _) (le_of_lt hpos)
    exact le_trans hdiv0 hdivle
  have hd12 : δ ≤ 1 / 2 := by simpa [δ] using hδ12
  have hge : ‖c i‖ ≤ ‖u‖ * δ := by
    have hg := planeResidual_ge_norm_c (x := x) e c he he_mem hc_orth i
    simpa [δ, u] using hg
  have hnormle : ‖u‖ ≤ 1 + ‖c i‖ := by
    simpa [u] using (graphVec_norm_le_one_add (x := x) e c he he_mem hc_orth i)
  have hineq : ‖c i‖ ≤ δ + δ * ‖c i‖ := by
    calc
      ‖c i‖ ≤ ‖u‖ * δ := hge
      _ ≤ (1 + ‖c i‖) * δ := mul_le_mul_of_nonneg_right hnormle hd0
      _ = δ + δ * ‖c i‖ := by ring
  have h1d : 0 < 1 - δ := by linarith
  have hmain : ‖c i‖ ≤ δ / (1 - δ) := by
    exact (le_div_iff₀ h1d).mpr (by nlinarith [hineq])
  have htail : δ / (1 - δ) ≤ 2 * δ := by
    exact (div_le_iff₀ h1d).mpr (by nlinarith [hd0, hd12])
  calc
    ‖c i‖ ≤ δ / (1 - δ) := hmain
    _ ≤ 2 * δ := htail
    _ = 2 * Submission.ProjectionDistance.planeResidual (graphSubspace e c) x := by rfl


end Submission.Bridge.ONGraph
