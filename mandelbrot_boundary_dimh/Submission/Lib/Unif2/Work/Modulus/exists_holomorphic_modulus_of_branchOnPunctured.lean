import Mathlib
import Submission.Lib.Unif2.Work.Modulus.puncturedHarmonic
import Submission.Lib.Unif2.Work.Modulus.growth_of_unitGreen
import Submission.Lib.Unif2.Work.Modulus.localHolomorphicModulus

/-!
# The global holomorphic modulus from a branch on the punctured surface

Let `X` be a connected complex one-manifold, `z₀ : X`, and `E : X → ℝ` a Green function with pole
`z₀` in the sense of `Work.UnitGreen.IsUnitGreenFunctionAt` (positive and harmonic off `z₀`,
logarithmic pole of coefficient one at `z₀`, decay at the ideal boundary).

Suppose that on the *punctured* surface `U = X ∖ {z₀}` there is already a **global** holomorphic
function `Φ` with `Φ u ≠ 0` and `‖Φ u‖ = exp (-(E u.1))` for every `u : U` — i.e. the multivalued
modulus `exp (-(E + iE*))` happens to be single-valued off the pole.  This module shows that `Φ`
then extends across the pole to a holomorphic function `Ψ : X → ℂ` with the same properties: the
Green function `E` has a global holomorphic modulus in the sense of
`Work.Modulus.HasTrivialModulusMonodromy`.

The mathematics is entirely local.  Since `E x → +∞` at `z₀`, we have `‖Φ u‖ = exp (-(E u.1)) → 0`,
so `Φ` is bounded near the puncture; Riemann's removable singularity theorem then extends `Φ`
holomorphically across `z₀` (with the value `0`, which is the only possible value).  The two
ingredients are therefore

* `holomorphicOnXAt_of_punctured` — a function on `X` that agrees with `Φ` off `z₀` is holomorphic
  at every `x ≠ z₀` (the chart of the open subspace `U` at `u` is the restriction of the ambient
  chart at `u`, `Work.Modulus.opensChartAt_symm_eqOn`);
* `tendsto_chartAt_symm_nhdsWithin` — the punctured-neighbourhood statement that lets us read the
  limit `Ψ x → 0` in the chart at `z₀`.
-/

open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set

namespace Work.Modulus

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A chart, restricted to the punctured neighbourhood of the image of its centre, still tends to
the centre in the punctured sense: `chartAt ℂ x` maps `𝓝[≠] (chartAt ℂ x) x` to `𝓝[≠] x`. -/
theorem tendsto_chartAt_symm_nhdsWithin (x : X) :
    Tendsto (chartAt ℂ x).symm (𝓝[≠] ((chartAt ℂ x) x)) (𝓝[≠] x) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h1 : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
      (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    have h2 : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    have h3 := h1.tendsto
    rw [h2] at h3
    exact h3.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((chartAt ℂ x).open_target.mem_nhds
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))] with z hz hzt
    have hz' : z ≠ (chartAt ℂ x) x := hz
    intro hcon
    have hxa : (chartAt ℂ x).symm z = x := hcon
    exact hz' (by rw [← (chartAt ℂ x).right_inv hzt, hxa])

/-- A function on `X` which agrees with a holomorphic function `Φ` on the punctured surface
`X ∖ {z₀}` is holomorphic at every point different from `z₀`. -/
theorem holomorphicOnXAt_of_punctured {z₀ : X} {Φ : puncturedOpens z₀ → ℂ} {Ψ : X → ℂ}
    (hΨ : ∀ x (hx : x ≠ z₀), Ψ x = Φ ⟨x, hx⟩)
    {x : X} (hx : x ≠ z₀) (h : Submission.HolomorphicOnXAt Φ ⟨x, hx⟩) :
    Submission.HolomorphicOnXAt Ψ x := by
  set u : puncturedOpens z₀ := ⟨x, hx⟩ with hu
  have h' : AnalyticAt ℂ (Φ ∘ (chartAt ℂ u).symm) ((chartAt ℂ u) u) := h
  rw [opensChartAt_apply (puncturedOpens z₀) u] at h'
  change AnalyticAt ℂ (Ψ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  refine h'.congr ?_
  filter_upwards [(chartAt ℂ u).open_target.mem_nhds
    (opensChartAt_mem_target (puncturedOpens z₀) u)] with z hz
  simp only [Function.comp_apply]
  have hcoe := opensChartAt_symm_eqOn (puncturedOpens z₀) u hz
  have hne : (chartAt ℂ x).symm z ≠ z₀ := by
    intro hc
    exact ((chartAt ℂ u).symm z).2 (by rw [hcoe]; exact hc)
  rw [hΨ ((chartAt ℂ x).symm z) hne]
  congr 1
  exact Subtype.ext hcoe

/-- **The global holomorphic modulus from a branch on the punctured surface.**

If `Φ` is a holomorphic, nowhere vanishing function on `X ∖ {z₀}` with modulus `exp (-E)`, then it
extends across the pole to a holomorphic `Ψ : X → ℂ`, still non-vanishing off `z₀` and with the
same modulus there.  (The extension vanishes at `z₀`, as it must: `exp (-E x) → 0`.) -/
theorem exists_holomorphic_modulus_of_branchOnPunctured
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)
    {Φ : puncturedOpens z₀ → ℂ} (hhol : Submission.HolomorphicOnX Φ Set.univ)
    (hne : ∀ u : puncturedOpens z₀, Φ u ≠ 0)
    (hmod : ∀ u : puncturedOpens z₀, ‖Φ u‖ = Real.exp (-(E u.1))) :
    ∃ Ψ : X → ℂ, Submission.HolomorphicOnX Ψ Set.univ ∧
      (∀ x, x ≠ z₀ → Ψ x ≠ 0) ∧ (∀ x, x ≠ z₀ → ‖Ψ x‖ = Real.exp (-(E x))) := by
  classical
  -- the candidate extension: `Φ` off the pole, and `0` at the pole
  let Ψ : X → ℂ := fun x => if h : x = z₀ then 0 else Φ ⟨x, h⟩
  have hΨeq : ∀ x (hx : x ≠ z₀), Ψ x = Φ ⟨x, hx⟩ := fun x hx => dif_neg hx
  have hΨ₀ : Ψ z₀ = 0 := dif_pos rfl
  have hΨnorm : ∀ x, x ≠ z₀ → ‖Ψ x‖ = Real.exp (-(E x)) := by
    intro x hx
    rw [hΨeq x hx]
    exact hmod ⟨x, hx⟩
  have hΨne : ∀ x, x ≠ z₀ → Ψ x ≠ 0 := by
    intro x hx
    rw [hΨeq x hx]
    exact hne ⟨x, hx⟩
  -- holomorphy away from the pole is transported from the punctured surface
  have hoff : ∀ x, x ≠ z₀ → Submission.HolomorphicOnXAt Ψ x :=
    fun x hx => holomorphicOnXAt_of_punctured hΨeq hx (hhol ⟨x, hx⟩ (mem_univ _))
  -- `E` tends to `+∞` at the pole, hence `Ψ` tends to `0` there
  have hΨtend : Tendsto Ψ (𝓝[≠] z₀) (𝓝 0) := by
    have hEtop : Tendsto E (𝓝[≠] z₀) atTop := by
      rw [Filter.tendsto_atTop]
      intro A
      obtain ⟨C₀, V₀, hV₀, hbnd₀⟩ := hE.2
      obtain ⟨V, hV, hVE⟩ := growth_of_unitGreen hV₀ hbnd₀ A
      filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with x hxV hxne
      exact (hVE x hxV hxne).le
    have hexp : Tendsto (fun x => Real.exp (-(E x))) (𝓝[≠] z₀) (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hEtop
    refine squeeze_zero_norm' (a := fun x => Real.exp (-(E x))) ?_ hexp
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hΨnorm x hx).le
  -- holomorphy at the pole: Riemann's removable singularity theorem
  have hzero : Submission.HolomorphicOnXAt Ψ z₀ := by
    change AnalyticAt ℂ (Ψ ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀)
    refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds ((chartAt ℂ z₀).open_target.mem_nhds
          ((chartAt ℂ z₀).map_source (mem_chart_source ℂ z₀)))] with w hw hwt
      have hxsrc : (chartAt ℂ z₀).symm w ∈ (chartAt ℂ z₀).source :=
        (chartAt ℂ z₀).map_target hwt
      have hxne : (chartAt ℂ z₀).symm w ≠ z₀ := by
        have hw' : w ≠ (chartAt ℂ z₀) z₀ := hw
        intro hcon
        exact hw' (by rw [← (chartAt ℂ z₀).right_inv hwt, hcon])
      have h := (Submission.HolomorphicOnXAt_iff_chart (f := Ψ) (x := (chartAt ℂ z₀).symm w)
        (y := z₀) hxsrc).mp (hoff _ hxne)
      rw [(chartAt ℂ z₀).right_inv hwt] at h
      exact h.differentiableAt
    · have hsymm : Tendsto (chartAt ℂ z₀).symm (𝓝[≠] ((chartAt ℂ z₀) z₀)) (𝓝[≠] z₀) :=
        tendsto_chartAt_symm_nhdsWithin z₀
      have hga : Ψ ((chartAt ℂ z₀).symm ((chartAt ℂ z₀) z₀)) = 0 := by
        rw [(chartAt ℂ z₀).left_inv (mem_chart_source ℂ z₀)]
        exact hΨ₀
      rw [continuousAt_iff_punctured_nhds]
      simpa only [Function.comp_apply, hga] using hΨtend.comp hsymm
  refine ⟨Ψ, ?_, hΨne, hΨnorm⟩
  intro x _
  by_cases hx : x = z₀
  · rw [hx]; exact hzero
  · exact hoff x hx

end Work.Modulus
