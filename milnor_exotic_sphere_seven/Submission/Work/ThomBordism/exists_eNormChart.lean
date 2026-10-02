import Mathlib
import Submission.Work.ThomBordism.boundaryChartAtTail
import Submission.Work.ThomBordism.PosAtlas.chartTrChangeSigned_gen
import Submission.Work.ThomBordism.PosAtlas.chartTr_eq_of_affine_transition

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A rescaled interior chart with a prescribed value at an interior point

For a `C¹` manifold with boundary `W` modelled on the half-space `𝓡∂ (n+1)`, a boundary point `y`,
and an interior point `x₀` in the source of the interior chart `icChart n W y`, we build an
`OpenPartialHomeomorph` `e` of `W` into the boundaryless model space with

* the **same source** as `icChart n W y` (so `y` itself is *not* in the source — indeed no chart
  into the boundaryless model space can contain a boundary point in its source),
* values in the closed half-space `{v | 0 ≤ v 0}`,
* `(e x₀) 0 > 0` and `‖e x₀‖ ≤ 1/2`,
* the **same chart transfer** of the Euclidean local generator at `x₀` as `icChart n W y`.

The construction is `e = icChart n W y` post-composed with the homothety `v ↦ c • v` of the model
for a small `c > 0`; the chart transfer is invariant because the homothety has positive determinant
(`PosAtlas.chartTr_eq_of_affine_transition`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold Topology

namespace Work.ThomBordism

/-! ## The homothety of the model space -/

/-- The homothety `v ↦ c • v` of the model space `ℝ^N`, `c ≠ 0`, as a homeomorphism. -/
noncomputable def scaleHomeo (N : ℕ) (c : ℝ) (hc : c ≠ 0) :
    EuclideanSpace ℝ (Fin N) ≃ₜ EuclideanSpace ℝ (Fin N) where
  toFun v := c • v
  invFun v := c⁻¹ • v
  left_inv v := by simp [smul_smul, inv_mul_cancel₀ hc]
  right_inv v := by simp [smul_smul, mul_inv_cancel₀ hc]
  continuous_toFun := continuous_const_smul c
  continuous_invFun := continuous_const_smul c⁻¹

@[simp] theorem scaleHomeo_apply (N : ℕ) (c : ℝ) (hc : c ≠ 0)
    (v : EuclideanSpace ℝ (Fin N)) : scaleHomeo N c hc v = c • v := rfl

@[simp] theorem scaleHomeo_symm_apply (N : ℕ) (c : ℝ) (hc : c ≠ 0)
    (v : EuclideanSpace ℝ (Fin N)) : (scaleHomeo N c hc).symm v = c⁻¹ • v := rfl

/-! ## The rescaled interior chart -/

/-- The chart `icChart n W y`, post-composed with a homothety of the model space: an
`OpenPartialHomeomorph` with the **same source** as `icChart n W y`. -/
noncomputable def normChart (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (y : W) (c : ℝ) (hc : c ≠ 0) :
    OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin (n + 1))) :=
  (Work.PTGeometric.icChart n W y).transHomeomorph (scaleHomeo (n + 1) c hc)

theorem normChart_source (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (y : W) (c : ℝ) (hc : c ≠ 0) :
    (normChart n W y c hc).source = (Work.PTGeometric.icChart n W y).source :=
  OpenPartialHomeomorph.transHomeomorph_source _ _

theorem normChart_apply (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (y : W) (c : ℝ) (hc : c ≠ 0) (z : W) :
    normChart n W y c hc z = c • (Work.PTGeometric.icChart n W y z) := by
  rw [normChart, OpenPartialHomeomorph.transHomeomorph_apply]
  rfl

/-- **Every value of the interior chart has strictly positive `0`-th coordinate**: the source of
`icChart n W y` consists of interior points, and the chart maps them into the interior of the
half-space model. -/
theorem icChart_coord_pos (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (y : W) {z : W} (hz : z ∈ (Work.PTGeometric.icChart n W y).source) :
    0 < ((Work.PTGeometric.icChart n W y) z) 0 := by
  have hmem : (Work.PTGeometric.icChart n W y) z ∈
      interior (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y).target := by
    rw [← Work.PTGeometric.icChart_target]
    exact (Work.PTGeometric.icChart n W y).map_source hz
  have h2 := interior_mono
    (extChartAt_target_subset_range (I := modelWithCornersEuclideanHalfSpace (n + 1)) y) hmem
  rw [interior_range_modelWithCornersEuclideanHalfSpace] at h2
  exact h2

/-! ## The main statement -/

theorem exists_eNormChart (n : ℕ) (hn : 1 ≤ n)
    (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {y : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {r : ℝ} (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    {x₀ : W} (hx₀ : x₀ ∈ Work.Orient.halfBallPiece (n + 1) W y r)
    (hx₀int : x₀ ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (hx₀e : x₀ ∈ (Work.PTGeometric.icChart n W y).source) :
    ∃ (e : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin (n + 1)))) (hx : x₀ ∈ e.source),
      e.source = (Work.PTGeometric.icChart n W y).source ∧
      (∀ z ∈ e.source, 0 ≤ (e z) 0) ∧
      (e x₀) 0 > 0 ∧ ‖e x₀‖ ≤ 1 / 2 ∧
      (Work.PTGeometric.HOF.chartTr e x₀ hx
          (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) (e x₀))
        = Work.PTGeometric.HOF.chartTr (Work.PTGeometric.icChart n W y) x₀ hx₀e
            (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) (Work.PTGeometric.icChart n W y x₀))) := by
  have hp0 : 0 < ((Work.PTGeometric.icChart n W y) x₀) 0 := icChart_coord_pos n W y hx₀e
  -- the scale factor
  obtain ⟨c, hcpos, hcle⟩ : ∃ c : ℝ, 0 < c ∧
      c * ‖((Work.PTGeometric.icChart n W y) x₀)‖ ≤ 1 / 2 := by
    refine ⟨1 / (2 * (‖((Work.PTGeometric.icChart n W y) x₀)‖ + 1)), by positivity, ?_⟩
    have hden : (0 : ℝ) < 2 * (‖((Work.PTGeometric.icChart n W y) x₀)‖ + 1) := by positivity
    have hmain : ‖((Work.PTGeometric.icChart n W y) x₀)‖
        / (2 * (‖((Work.PTGeometric.icChart n W y) x₀)‖ + 1)) ≤ 1 / 2 := by
      rw [div_le_iff₀ hden]
      linarith [norm_nonneg ((Work.PTGeometric.icChart n W y) x₀)]
    calc 1 / (2 * (‖((Work.PTGeometric.icChart n W y) x₀)‖ + 1))
          * ‖((Work.PTGeometric.icChart n W y) x₀)‖
        = ‖((Work.PTGeometric.icChart n W y) x₀)‖
            / (2 * (‖((Work.PTGeometric.icChart n W y) x₀)‖ + 1)) := by ring
      _ ≤ 1 / 2 := hmain
  have hcne : c ≠ 0 := ne_of_gt hcpos
  -- the chart
  have hx : x₀ ∈ (normChart n W y c hcne).source := by
    rw [normChart_source]; exact hx₀e
  have hsrc : (normChart n W y c hcne).source = (Work.PTGeometric.icChart n W y).source :=
    normChart_source n W y c hcne
  have hnn : ∀ z ∈ (normChart n W y c hcne).source, 0 ≤ (normChart n W y c hcne z) 0 := by
    intro z hz
    have hzs : z ∈ (Work.PTGeometric.icChart n W y).source := by
      rwa [normChart_source] at hz
    rw [normChart_apply]
    simp only [PiLp.smul_apply, smul_eq_mul]
    exact mul_nonneg (le_of_lt hcpos) (le_of_lt (icChart_coord_pos n W y hzs))
  have hpos : (normChart n W y c hcne x₀) 0 > 0 := by
    rw [normChart_apply]
    simp only [PiLp.smul_apply, smul_eq_mul]
    exact mul_pos hcpos hp0
  have hnorm : ‖normChart n W y c hcne x₀‖ ≤ 1 / 2 := by
    rw [normChart_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    exact hcle
  -- the transfer of the local generator
  have hbij : Function.Bijective
      ⇑(c • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) := by
    constructor
    · intro u v huv
      have huv' : c • u = c • v := by simpa using huv
      exact smul_right_injective _ hcne huv'
    · intro w
      exact ⟨c⁻¹ • w, by simp [smul_smul, mul_inv_cancel₀ hcne, inv_mul_cancel₀ hcne]⟩
  have htrans : ∀ z ∈ (Work.PTGeometric.icChart n W y).target,
      normChart n W y c hcne ((Work.PTGeometric.icChart n W y).symm z)
        = (c • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
            EuclideanSpace ℝ (Fin (n + 1)))) z + 0 := by
    intro z hz
    rw [normChart_apply, (Work.PTGeometric.icChart n W y).right_inv hz]
    simp
  have hdet : 0 < LinearMap.det
      (↑(c • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (n + 1)))) :
        EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one,
      LinearMap.det_smul]
    have hone : LinearMap.det
        (1 : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) = 1 := by
      rw [show (1 : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin (n + 1))) = LinearMap.id from rfl, LinearMap.det_id]
    rw [hone, mul_one, finrank_euclideanSpace, Fintype.card_fin]
    exact pow_pos hcpos _
  have htr := (PosAtlas.chartTr_eq_of_affine_transition (n := n + 1) (by omega)
      (Work.PTGeometric.icChart n W y) (normChart n W y c hcne)
      (c • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))))
      hbij 0 htrans hdet x₀ hx₀e hx)
  exact ⟨normChart n W y c hcne, hx, hsrc, hnn, hpos, hnorm, htr.symm⟩

end Work.ThomBordism
