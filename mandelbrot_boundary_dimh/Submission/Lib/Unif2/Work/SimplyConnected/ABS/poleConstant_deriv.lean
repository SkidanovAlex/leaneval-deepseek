import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.modulusLP_local
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs

/-!
# The derivative of a holomorphic modulus at its pole, without decay

Let `X` be a complex one-manifold, `x₀ : X`, `E : X → ℝ` harmonic off `x₀` with a *unit*
logarithmic pole at `x₀` (`Work.SimplyConnected.ABS.HasLogPoleOn`), and `Φ` a holomorphic function
on `X` with `‖Φ x‖ = exp (-(E x))` off `x₀` and `Φ x₀ = 0` (a *modulus* of `E`).

This file computes the norm of the derivative of `Φ` at its zero `x₀`: it is the exponential of the
*negative pole constant* of `E`,

  `‖Φ'‖ = exp (-c)`,  where  `c = lim_{w → a} ( E (c⁻¹ w) + log ‖w - a‖ )`,  `a := c x₀`,

`c := chartAt ℂ x₀`.  The limit exists by the local pole expansion
(`Work.ModulusLP.localPoleExpansion`: `E x = -log ‖c x - a‖ + H (c x)` with `H` harmonic), and the
value of the derivative follows from
`‖Φ (c⁻¹ w)‖ / ‖w - a‖ = exp (-(E (c⁻¹ w) + log ‖w - a‖)) → exp (-c)`
as `w → a`, together with `HasDerivAt.tendsto_slope` and `norm_slope` for the slope of `Φ ∘ c⁻¹`.

This is the analytic core of the rigidity `‖f x‖ = exp (-(E x))` for the extremal maximiser:
`hmax` applied to `Φ ∈ Submission.extremalFamily x₀` gives `‖f'(x₀)‖ ≥ ‖Φ'(x₀)‖ = exp (-c)`, which is
exactly the inequality `u(x₀) ≥ 0` that the maximum principle needs for `u := E + log ‖f‖ ≤ 0`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X}

/-- **The pole constant of a unit logarithmic pole exists.** -/
theorem exists_poleConstant {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {x₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀ E) :
    ∃ c : ℝ, Filter.Tendsto
      (fun w : ℂ => E ((chartAt ℂ x₀).symm w) + Real.log ‖w - (chartAt ℂ x₀) x₀‖)
      (𝓝[≠] ((chartAt ℂ x₀) x₀)) (𝓝 c) := by
  obtain ⟨ρ, hρ, H, hH, hexp⟩ := Work.ModulusLP.localPoleExpansion (z₀ := x₀) hEharm hpole
  obtain ⟨ε, hε, hεsub, -⟩ := Work.ModulusLP.chartPoleBound (z₀ := x₀) hEharm hpole
  set a : ℂ := (chartAt ℂ x₀) x₀ with ha
  set r : ℝ := min ρ ε with hr
  have hrpos : 0 < r := lt_min hρ hε
  have hrρ : r ≤ ρ := min_le_left _ _
  have hrε : r ≤ ε := min_le_right _ _
  have hHcont : ContinuousAt H a := (hH a (Metric.mem_ball_self hρ)).1.continuousAt
  have hev : (fun w : ℂ => E ((chartAt ℂ x₀).symm w) + Real.log ‖w - a‖) =ᶠ[𝓝[≠] a] H := by
    have h1' : ∀ᶠ w : ℂ in 𝓝 a, w ∈ Metric.ball a r :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrpos)
    have h1 : ∀ᶠ w : ℂ in 𝓝[≠] a, w ∈ Metric.ball a r :=
      h1'.filter_mono nhdsWithin_le_nhds
    filter_upwards [h1, self_mem_nhdsWithin] with w hwball hwne
    have hwρ : w ∈ Metric.ball a ρ := Metric.ball_subset_ball hrρ hwball
    have hwt : w ∈ (chartAt ℂ x₀).target := hεsub (Metric.ball_subset_ball hrε hwball)
    have hcs : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm w) = w := (chartAt ℂ x₀).right_inv hwt
    have hwsrc : (chartAt ℂ x₀).symm w ∈ (chartAt ℂ x₀).source := (chartAt ℂ x₀).map_target hwt
    have hmem : (chartAt ℂ x₀).symm w ∈ Submission.chartBall (chartAt ℂ x₀) a ρ :=
      ⟨hwsrc, by rw [Set.mem_preimage, hcs]; exact hwρ⟩
    have hne : (chartAt ℂ x₀).symm w ≠ x₀ := by
      intro hcon
      refine hwne ?_
      have hwa : w = a := by rw [← hcs, hcon]
      exact hwa
    have h := hexp ((chartAt ℂ x₀).symm w) hmem hne
    rw [hcs] at h
    rw [h]
    ring
  exact ⟨H a, (hHcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm⟩

/-- **The norm of the derivative of a modulus at the pole is `exp (-c)`.** -/
theorem norm_deriv_modulus_eq_exp_neg_poleConstant {E : X → ℝ} {Φ : X → ℂ}
    (hΦhol : Submission.HolomorphicOnX Φ Set.univ)
    (hΦzero : Φ x₀ = 0)
    (hΦmod : ∀ x : X, x ≠ x₀ → ‖Φ x‖ = Real.exp (-(E x)))
    (htgt : ∀ᶠ w : ℂ in 𝓝[≠] ((chartAt ℂ x₀) x₀), w ∈ (chartAt ℂ x₀).target)
    {c : ℝ}
    (hc : Filter.Tendsto (fun w : ℂ => E ((chartAt ℂ x₀).symm w)
      + Real.log ‖w - (chartAt ℂ x₀) x₀‖) (𝓝[≠] ((chartAt ℂ x₀) x₀)) (𝓝 c)) :
    ‖deriv (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ = Real.exp (-c) := by
  set a : ℂ := (chartAt ℂ x₀) x₀ with ha
  set F : ℂ → ℂ := Φ ∘ (chartAt ℂ x₀).symm with hF
  have hsymm : (chartAt ℂ x₀).symm a = x₀ := by
    rw [ha]; exact (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)
  have hFa : AnalyticAt ℂ F a := hΦhol x₀ (mem_univ x₀)
  have hF0 : F a = 0 := by
    simp only [hF, Function.comp_apply, hsymm]
    exact hΦzero
  have hderiv : HasDerivAt F (deriv F a) a := hFa.differentiableAt.hasDerivAt
  have hslope : Filter.Tendsto (fun w : ℂ => ‖slope F a w‖) (𝓝[≠] a) (𝓝 ‖deriv F a‖) :=
    hderiv.tendsto_slope.norm
  have hratio : ∀ᶠ w : ℂ in 𝓝[≠] a,
      ‖slope F a w‖ = Real.exp (-(E ((chartAt ℂ x₀).symm w) + Real.log ‖w - a‖)) := by
    filter_upwards [htgt, self_mem_nhdsWithin] with w hwt hwne
    have hcs : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm w) = w := (chartAt ℂ x₀).right_inv hwt
    have hne : (chartAt ℂ x₀).symm w ≠ x₀ := by
      intro hcon
      refine hwne ?_
      have hwa : w = a := by rw [← hcs, hcon]
      exact hwa
    have hna : 0 < ‖w - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwne)
    rw [slope_def_field, hF0, sub_zero, norm_div]
    have hnorm : ‖F w‖ = ‖Φ ((chartAt ℂ x₀).symm w)‖ := rfl
    rw [hnorm, hΦmod ((chartAt ℂ x₀).symm w) hne]
    have harith : -(E ((chartAt ℂ x₀).symm w) + Real.log ‖w - a‖)
        = -(E ((chartAt ℂ x₀).symm w)) + -(Real.log ‖w - a‖) := by ring
    have h2 : Real.exp (-(Real.log ‖w - a‖)) = (‖w - a‖)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hna]
    rw [harith, Real.exp_add, h2, div_eq_mul_inv]
  have hlim1 := hslope.congr' hratio
  have hlim2 : Filter.Tendsto (fun w : ℂ =>
      Real.exp (-(E ((chartAt ℂ x₀).symm w) + Real.log ‖w - a‖))) (𝓝[≠] a)
      (𝓝 (Real.exp (-c))) := (Real.continuous_exp.tendsto (-c)).comp hc.neg
  exact tendsto_nhds_unique hlim1 hlim2

end Work.SimplyConnected.ABS
