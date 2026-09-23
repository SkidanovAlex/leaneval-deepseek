import Mathlib
import Submission.Work.OddBound.PolygonChart

/-!
# Criticality is chart-independent (the `C¹` chart-change step)

`Work.OddBound.IsCriticalChart H' f z` says that *some* atlas chart `e₀` around `z` has vanishing
coordinate derivative at `e₀ z`.  Since the coordinate derivative of `f` at a point is a
chart-dependent object, that notion is only meaningful if it is chart-independent: this module
proves that in **every** atlas chart `e` around `z` in which the coordinate expression
`f ∘ e.symm` is `C¹` at `e z` (hence genuinely differentiable, so that `fderiv` is not a junk
value) the coordinate derivative vanishes at `e z`.

The proof is the chain rule along the chart transition.  Write `τ = e.symm ≫ₕ e₀` for the
transition from `e`-coordinates to `e₀`-coordinates; on a neighbourhood of `e z` the two
coordinate expressions agree,
`f ∘ e.symm = (f ∘ e₀.symm) ∘ τ`,
because `e₀.symm (e₀ (e.symm y)) = e.symm y` as soon as `e.symm y ∈ e₀.source`.  The transition
`τ` is `C¹` at `e z`: it belongs to `contDiffGroupoid 1 𝓘(ℝ, H')`, and in the identity model that
groupoid is exactly the collection of `C¹` open partial homeomorphisms.  Since `f ∘ e₀.symm` is
differentiable at `τ (e z) = e₀ z`, the chain rule gives

`fderiv ℝ (f ∘ e.symm) (e z) = (fderiv ℝ (f ∘ e₀.symm) (e₀ z)).comp (fderiv ℝ τ (e z)) = 0`.
-/

namespace Work.OddBound.mountainPass3

open scoped Manifold ContDiff

/-- **Chart changes of a `C¹` manifold on the identity model are `C¹`.**
For `e, e₀` in the atlas of a `C¹` charted space `P` modelled on the normed space `H'` itself,
the transition map `e.symm ≫ₕ e₀` (from `e`-coordinates to `e₀`-coordinates) is `C¹` on its
source `(e.symm ≫ₕ e₀).source = e.target ∩ e.symm ⁻¹' e₀.source`. -/
theorem contDiffOn_symm_trans_of_mem_atlas
    {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
    [IsManifold (𝓘(ℝ, H')) 1 P] {e e₀ : OpenPartialHomeomorph P H'}
    (he : e ∈ atlas H' P) (he₀ : e₀ ∈ atlas H' P) :
    ContDiffOn ℝ 1 (⇑(e.symm ≫ₕ e₀)) (e.symm ≫ₕ e₀).source := by
  -- The transition lies in the `C¹` structure groupoid of the identity model, where membership
  -- in `contDiffGroupoid 1 𝓘(ℝ, H')` means precisely `C¹`-ness of the transition.
  have h := (contDiffGroupoid 1 (𝓘(ℝ, H'))).compatible he he₀
  rw [contDiffGroupoid] at h
  rw [mem_groupoid_of_pregroupoid] at h
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.range_id, Set.preimage_id, Set.inter_univ] at h
  exact h.1

theorem fderiv_chart_expression_eq_zero_of_isCriticalChart
    {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
    [IsManifold (𝓘(ℝ, H')) 1 P] {f : P → ℝ} {z : P}
    (hcrit : Work.OddBound.IsCriticalChart H' f z)
    (hsmooth : ∀ (e : OpenPartialHomeomorph P H'), e ∈ atlas H' P → z ∈ e.source →
      ContDiffAt ℝ 1 (fun x : H' => f (e.symm x)) (e z))
    (e : OpenPartialHomeomorph P H') (he : e ∈ atlas H' P) (hz : z ∈ e.source) :
    fderiv ℝ (fun x : H' => f (e.symm x)) (e z) = 0 := by
  -- Unpack the critical chart `e₀` supplied by `hcrit`.
  obtain ⟨e₀, he₀, hz₀, hder₀⟩ := hcrit
  -- `τ` is the transition from `e`-coordinates to `e₀`-coordinates.
  set τ : OpenPartialHomeomorph H' H' := e.symm ≫ₕ e₀ with hτ
  -- `e z` lies in the source of `τ` (the source is `e.target ∩ e.symm ⁻¹' e₀.source`).
  have hez : e z ∈ τ.source := by
    rw [hτ, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff]
    refine ⟨e.map_source hz, ?_⟩
    change (e.symm : H' → P) (e z) ∈ e₀.source
    rw [e.left_inv hz]
    exact hz₀
  -- And `τ` sends `e z` to `e₀ z`.
  have hτz : τ (e z) = e₀ z := by
    rw [hτ, OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.left_inv e hz]
  -- `τ` is `C¹`, hence differentiable, at `e z`.
  have hτdiff : DifferentiableAt ℝ (⇑τ) (e z) := by
    have h : ContDiffOn ℝ 1 (⇑τ) τ.source := by
      rw [hτ]
      exact contDiffOn_symm_trans_of_mem_atlas he he₀
    exact (h.contDiffAt (τ.open_source.mem_nhds hez)).differentiableAt one_ne_zero
  -- `f ∘ e₀.symm` is differentiable at `τ (e z) = e₀ z`, by hypothesis (`fderiv = 0` alone would
  -- be vacuous for a non-differentiable expression, since `fderiv` is `0` by convention there).
  have hgz : DifferentiableAt ℝ (fun x : H' => f (e₀.symm x)) (τ (e z)) := by
    rw [hτz]
    exact (hsmooth e₀ he₀ hz₀).differentiableAt one_ne_zero
  -- On the (open) source of `τ` the two coordinate expressions agree.
  have heq : (fun y : H' => f (e.symm y)) =ᶠ[nhds (e z)] (fun y : H' => f (e₀.symm (τ y))) := by
    filter_upwards [τ.open_source.mem_nhds hez] with y hy
    have hy' : e.symm y ∈ e₀.source := by
      have h2 := hy
      rw [hτ, OpenPartialHomeomorph.trans_source] at h2
      exact h2.2
    show f (e.symm y) = f (e₀.symm (τ y))
    rw [hτ, OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.left_inv e₀ hy']
  -- Chain rule along the chart change; the outer derivative is zero by criticality of `e₀`.
  calc fderiv ℝ (fun x : H' => f (e.symm x)) (e z)
      = fderiv ℝ (fun y : H' => f (e₀.symm (τ y))) (e z) := heq.fderiv_eq
    _ = (fderiv ℝ (fun x : H' => f (e₀.symm x)) (τ (e z))).comp (fderiv ℝ (⇑τ) (e z)) :=
          fderiv_comp (f := ⇑τ) (g := fun x : H' => f (e₀.symm x)) (x := e z) hgz hτdiff
    _ = 0 := by rw [hτz, hder₀, ContinuousLinearMap.zero_comp]

end Work.OddBound.mountainPass3
