import Mathlib

namespace Work.OddBound.mountainPass3

open scoped Manifold ContDiff Topology
open Filter

/-- Chart-independence of the coordinate expression of a function `P → ℝ` on a `C^n` manifold
modelled on the boundaryless model `𝓘(ℝ, H')`.

If for *some* chart `e₀` in the atlas at `z` the expression `x ↦ f (e₀.symm x)` is `C^n` at
`e₀ z`, then for *every* chart `e` in the atlas with `z ∈ e.source` the expression
`x ↦ f (e.symm x)` is `C^n` at `e z`. This is the standard "chart independence" of the
smoothness of a function; the point is that the change of coordinates `e₀ ∘ e.symm` is `C^n`
because `e₀` and `e` both belong to the maximal `C^n` atlas and hence are compatible. -/
theorem contDiffAt_chart_expression_of_mem_atlas
    {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] {n : ℕ}
    [IsManifold (𝓘(ℝ, H')) n P] {f : P → ℝ} {z : P}
    (hsm : ∃ e₀ : OpenPartialHomeomorph P H', e₀ ∈ atlas H' P ∧ z ∈ e₀.source ∧
      ContDiffAt ℝ n (fun x : H' => f (e₀.symm x)) (e₀ z))
    (e : OpenPartialHomeomorph P H') (he : e ∈ atlas H' P) (hz : z ∈ e.source) :
    ContDiffAt ℝ n (fun x : H' => f (e.symm x)) (e z) := by
  obtain ⟨e₀, he₀, hz₀, hd⟩ := hsm
  -- Both charts lie in the maximal `C^n` atlas.
  have hmax₀ : e₀ ∈ IsManifold.maximalAtlas 𝓘(ℝ, H') n P := IsManifold.subset_maximalAtlas he₀
  have hmax : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, H') n P := IsManifold.subset_maximalAtlas he
  -- On `ℝ` (a manifold over itself) the identity chart is in the maximal atlas; extending it
  -- by the trivial model gives the identity, so the target chart can be taken to be `refl ℝ`.
  have hself : OpenPartialHomeomorph.refl ℝ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℝ) n ℝ := by
    have h := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ,ℝ)) (n := n) (M := ℝ) (f z)
    rwa [chartAt_self_eq] at h
  have hmem : f z ∈ (OpenPartialHomeomorph.refl ℝ).source := by
    rw [OpenPartialHomeomorph.refl_source]; exact Set.mem_univ _
  -- Continuity of `f` at `z`, obtained by pulling back along the chart `e₀`.
  have hcont : ContinuousAt f z := by
    have h1 : ContinuousAt (fun y : P => f (e₀.symm (e₀ y))) z :=
      (hd.continuousAt).comp (e₀.continuousAt hz₀)
    have heq : (fun y : P => f (e₀.symm (e₀ y))) =ᶠ[𝓝 z] f := by
      filter_upwards [e₀.open_source.mem_nhds hz₀] with y hy
      simp [e₀.left_inv hy]
    exact h1.congr heq
  -- Reinterpret the hypothesis as `ContMDiffAt` of `f` (this is where chart independence
  -- is built in), then read it back in the chart `e`.
  have key : ContMDiffAt 𝓘(ℝ, H') 𝓘(ℝ, ℝ) n f z := by
    rw [contMDiffAt_iff_of_mem_maximalAtlas (e := e₀) (e' := OpenPartialHomeomorph.refl ℝ)
      hmax₀ hself hz₀ hmem]
    refine ⟨hcont, ?_⟩
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def, id_eq,
      Set.range_id, OpenPartialHomeomorph.refl_apply]
    exact contDiffWithinAt_univ.mpr hd
  rw [contMDiffAt_iff_of_mem_maximalAtlas (e := e) (e' := OpenPartialHomeomorph.refl ℝ)
    hmax hself hz hmem] at key
  have h := key.2
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def, id_eq,
    Set.range_id, OpenPartialHomeomorph.refl_apply] at h
  exact contDiffWithinAt_univ.mp h

end Work.OddBound.mountainPass3
