import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Topology Manifold
open Filter

namespace Work.ThomBordism

theorem extChart_transition_det_pos (k : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (8 + k + 1)) M]
    (hid : ∀ (x y : M),
      x ∉ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary M →
      y ∉ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary M →
      ∀ p ∈ (extChartAt (modelWithCornersEuclideanHalfSpace (8 + k + 1)) x).source ∩
             (extChartAt (modelWithCornersEuclideanHalfSpace (8 + k + 1)) y).source,
        (extChartAt (modelWithCornersEuclideanHalfSpace (8 + k + 1)) x) p =
          (extChartAt (modelWithCornersEuclideanHalfSpace (8 + k + 1)) y) p) :
    ∀ (x y : M),
      x ∉ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary M →
      y ∉ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary M →
      ∀ z ∈ (extChartAt (modelWithCornersEuclideanHalfSpace (8 + k + 1)) x).target ∩
          (extChartAt (modelWithCornersEuclideanHalfSpace (8 + k + 1)) x).symm ⁻¹'
            (extChartAt (modelWithCornersEuclideanHalfSpace (8 + k + 1)) y).source,
        z 0 > 0 →
        (0 : ℝ) < LinearMap.det
          ((fderiv ℝ (fun w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
            (extChartAt (modelWithCornersEuclideanHalfSpace (8 + k + 1)) y)
              ((extChartAt (modelWithCornersEuclideanHalfSpace (8 + k + 1)) x).symm w)) z)
            : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ]
              EuclideanSpace ℝ (Fin ((8 + k) + 1))) := by
  intro x y hx hy z hz hzpos
  obtain ⟨hz1, hz2⟩ := hz
  -- Abbreviate the model with corners.
  set I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin ((8 + k) + 1)))
      (EuclideanHalfSpace ((8 + k) + 1)) := modelWithCornersEuclideanHalfSpace (8 + k + 1) with hI
  -- The `x`-chart target is a neighbourhood of `z`: it contains the open set
  -- `{w | 0 < w 0} ∩ (symm x) ⁻¹' (chart target)` (this is where `z 0 > 0` is used).
  have htarget_nhds : (extChartAt I x).target ∈ 𝓝 z := by
    rw [extChartAt_target]
    have hzI : z ∈ (I.symm : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →
        EuclideanHalfSpace ((8 + k) + 1)) ⁻¹'
        (chartAt (EuclideanHalfSpace ((8 + k) + 1)) x).target := by
      have h := hz1
      rw [hI] at h
      rw [extChartAt_target] at h
      exact h.1
    have hzint : z ∈ interior (Set.range (I : EuclideanHalfSpace ((8 + k) + 1) →
        EuclideanSpace ℝ (Fin ((8 + k) + 1)))) := by
      have hrange : Set.range (I : EuclideanHalfSpace ((8 + k) + 1) →
          EuclideanSpace ℝ (Fin ((8 + k) + 1))) =
          {y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) | 0 ≤ y.ofLp 0} := by
        change Set.range (I.toPartialEquiv : EuclideanHalfSpace ((8 + k) + 1) →
          EuclideanSpace ℝ (Fin ((8 + k) + 1))) = _
        rw [ModelWithCorners.range_eq_target]
        rfl
      rw [hrange, interior_halfSpace]
      exact hzpos
    have hU : IsOpen ((I.symm : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →
          EuclideanHalfSpace ((8 + k) + 1)) ⁻¹'
            (chartAt (EuclideanHalfSpace ((8 + k) + 1)) x).target ∩
        interior (Set.range (I : EuclideanHalfSpace ((8 + k) + 1) →
          EuclideanSpace ℝ (Fin ((8 + k) + 1))))) :=
      (I.continuous_invFun.isOpen_preimage _
        (chartAt (EuclideanHalfSpace ((8 + k) + 1)) x).open_target).inter isOpen_interior
    refine mem_of_superset (hU.mem_nhds ⟨hzI, hzint⟩) ?_
    intro w hw
    exact ⟨hw.1, interior_subset hw.2⟩
  -- `(symm x)` is continuous at `z`, so the preimage of the (open) `y`-chart source is a
  -- neighbourhood of `z`.
  have hsymm_nhds : (extChartAt I x).symm ⁻¹' (extChartAt I y).source ∈ 𝓝 z := by
    have hcont : ContinuousAt (extChartAt I x).symm z :=
      (continuousOn_extChartAt_symm (I := I) x).continuousAt htarget_nhds
    exact hcont.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) y).mem_nhds hz2)
  -- On this neighbourhood, the transition map is the identity.
  have hevent : (fun w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
      (extChartAt I y) ((extChartAt I x).symm w)) =ᶠ[𝓝 z] id := by
    filter_upwards [htarget_nhds, hsymm_nhds] with w hw1 hw2
    calc (extChartAt I y) ((extChartAt I x).symm w)
        = (extChartAt I x) ((extChartAt I x).symm w) := by
          have hx' : x ∉ I.boundary M := hx
          have hy' : y ∉ I.boundary M := hy
          exact (hid x y hx' hy' _ ⟨(extChartAt I x).map_target hw1, hw2⟩).symm
      _ = w := (extChartAt I x).right_inv hw1
  have hfderiv : fderiv ℝ (fun w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
      (extChartAt I y) ((extChartAt I x).symm w)) z = fderiv ℝ id z := hevent.fderiv_eq
  rw [hfderiv, fderiv_id]
  simp

end Work.ThomBordism
