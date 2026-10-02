import Mathlib
import Submission.Work.Morse.flow_basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false in
/-- A solution of the chart equation `f' = chartVF v x₀ ∘ f` whose values lie in the chart target
gives an integral curve of `v` in `M`. -/
theorem isMIntegralCurveOn_chartVF {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {v : (x : M) → TangentSpace (𝓡 n) x} {x₀ : M} {s : Set ℝ}
    {γ : ℝ → M} {f : ℝ → EuclideanSpace ℝ (Fin n)}
    (hγ : ∀ t ∈ s, γ t = (extChartAt (𝓡 n) x₀).symm (f t))
    (hmem : ∀ t ∈ s, f t ∈ (extChartAt (𝓡 n) x₀).target)
    (hf : ∀ t ∈ s, HasDerivAt f (chartVF v x₀ (f t)) t) :
    IsMIntegralCurveOn γ v s := by
  -- It suffices to check the property for the (globally defined) curve `(extChartAt _ x₀).symm ∘ f`,
  -- and then transfer along the equality `γ = (extChartAt _ x₀).symm ∘ f` on `s`.
  have hmain : ∀ t ∈ s, HasMFDerivAt (𝓘(ℝ,ℝ)) (𝓡 n)
      ((extChartAt (𝓡 n) x₀).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((extChartAt (𝓡 n) x₀).symm (f t)))) := by
    intro t ht
    have hy : f t ∈ (extChartAt (𝓡 n) x₀).target := hmem t ht
    -- continuity
    refine ⟨(continuousAt_extChartAt_symm'' hy).comp (hf t ht).continuousAt, ?_⟩
    -- the manifold derivative part: reduce to a statement about functions of the model space
    apply HasDerivWithinAt.hasFDerivWithinAt
    simp only [mfld_simps, hasDerivWithinAt_univ]
    set z : M := (chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm (f t) with hzdef
    -- the derivative of the chart expression is an element of the model space `EuclideanSpace`
    change HasDerivAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) z) ∘ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm ∘ f)
      (v z : EuclideanSpace ℝ (Fin n)) t
    have hzy : (extChartAt (𝓡 n) x₀) z = f t := by
      rw [hzdef]
      exact (extChartAt (𝓡 n) x₀).right_inv hy
    have hft1 : z ∈ (extChartAt (𝓡 n) x₀).source := (extChartAt (𝓡 n) x₀).map_target hy
    have hft2 : z ∈ (extChartAt (𝓡 n) z).source := mem_extChartAt_source z
    -- the coordinate change `extChartAt _ z ∘ (extChartAt _ x₀).symm` is differentiable at `f t`
    have hG : HasFDerivAt
        ((chartAt (EuclideanSpace ℝ (Fin n)) z) ∘ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm)
        (tangentCoordChange (𝓡 n) x₀ z z) (f t) := by
      have h1 := (hasFDerivWithinAt_tangentCoordChange (I := 𝓡 n) (x := x₀) (y := z) (z := z)
        ⟨hft1, hft2⟩).hasFDerivAt (by rw [ModelWithCorners.range_eq_univ]; exact Filter.univ_mem)
      rwa [hzy] at h1
    -- the chart expression of `v` in the two charts
    have hcv : chartVF v x₀ (f t) =
        (tangentCoordChange (𝓡 n) z x₀ z) (v z : EuclideanSpace ℝ (Fin n)) := by
      rw [hzdef]
      rfl
    -- composing the two derivatives gives back `v (γ t)`
    have hkey : (tangentCoordChange (𝓡 n) x₀ z z) (chartVF v x₀ (f t)) =
        (v z : EuclideanSpace ℝ (Fin n)) :=
      calc (tangentCoordChange (𝓡 n) x₀ z z) (chartVF v x₀ (f t))
          = (tangentCoordChange (𝓡 n) x₀ z z)
              ((tangentCoordChange (𝓡 n) z x₀ z) (v z : EuclideanSpace ℝ (Fin n))) := by rw [hcv]
        _ = (tangentCoordChange (𝓡 n) z z z) (v z : EuclideanSpace ℝ (Fin n)) :=
              tangentCoordChange_comp (I := 𝓡 n) (w := z) (x := x₀) (y := z) (z := z)
                (v := (v z : EuclideanSpace ℝ (Fin n))) ⟨⟨hft2, hft1⟩, hft2⟩
        _ = (v z : EuclideanSpace ℝ (Fin n)) :=
              tangentCoordChange_self (I := 𝓡 n) (x := z) (z := z)
                (v := (v z : EuclideanSpace ℝ (Fin n))) hft2
    have hf' : HasDerivAt f ((tangentCoordChange (𝓡 n) z x₀ z) (v z : EuclideanSpace ℝ (Fin n))) t := by
      rw [← hcv]
      exact hf t ht
    exact (hG.comp_hasDerivAt t hf').congr_deriv hkey
  intro t ht
  rw [hγ t ht]
  exact ((hmain t ht).hasMFDerivWithinAt).congr_mono (fun u hu => hγ u hu) (hγ t ht)
    (fun _ hu => hu)

end Work.Morse
