import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.Modulus.poleOrderModulus

namespace Work.SimplyConnected.ABS

open Filter Set
open scoped Topology

/-- **The zero at the pole is simple.**  `Φ` is holomorphic at `x₀ ∈ Ω ⊆ X` (with `X` a Riemann
surface, `Ω` open), its modulus on `Ω ∖ {x₀}` is `exp (-E)`, and `E` has a *bounded* logarithmic pole at
`x₀` in the preferred chart there: `|E x + log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖| ≤ C` for all `x`
near `x₀` that lie in `Ω`.  Then in the preferred chart at `x₀`, `Φ` has a zero of order exactly one.

Equivalently, with `a := (chartAt ℂ x₀) x₀`, the conclusion is: there is `H` analytic at `a` with
`H a ≠ 0` and `Φ ∘ (chartAt ℂ x₀).symm =ᶠ[nhds a] (fun w : ℂ => (w - a) * H w)`.  This is exactly the
simple-zero clause of `Work.SimplyConnected.ABS.IsModulusOn`.

Recipe: put `g := Φ ∘ (chartAt ℂ x₀).symm` and `a := (chartAt ℂ x₀) x₀`.  Then `g` is analytic at `a`
(because `Submission.HolomorphicOnXAt Φ x₀` *is* that assertion), and for `w` near `a`, `w ≠ a`, with
`x := (chartAt ℂ x₀).symm w` one has `‖g w‖ = ‖Φ x‖ = exp (-(E x))`, while
`Work.Modulus.exp_bounds_of_abs_add_log` turns the pole bound `|E x + log ‖w - a‖| ≤ C` into
`exp (-C) * ‖w - a‖ ≤ ‖g w‖ ≤ exp C * ‖w - a‖` (`w ≠ a` gives `0 < ‖w - a‖`).  A holomorphic function
with such a two-sided *linear* growth bound has a zero of order one: that is exactly
`Work.Modulus.simpleZeroOfGrowth`, which produces the required `H`.  Only analyticity of `Φ` at `x₀`,
the pole bound and the modulus identity are used -- no harmonicity of `E` and no global hypothesis. -/
theorem exists_simpleZero_of_modulus_exp {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) {x₀ : X} (hx₀ : x₀ ∈ Ω) {E : X → ℝ} {Φ : X → ℂ}
    (hpole : ∃ C : ℝ, ∃ V : Set X, V ∈ nhds x₀ ∧ ∀ x ∈ V, x ∈ Ω → x ≠ x₀ →
      |E x + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖| ≤ C)
    (hhol : Submission.HolomorphicOnXAt Φ x₀)
    (hmod : ∀ x ∈ Ω, x ≠ x₀ → ‖Φ x‖ = Real.exp (-(E x))) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
      (Φ ∘ (chartAt ℂ x₀).symm) =ᶠ[nhds ((chartAt ℂ x₀) x₀)]
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w) := by
  obtain ⟨C, V, hV, hVbnd⟩ := hpole
  set c := chartAt ℂ x₀ with hc
  set a : ℂ := c x₀ with ha
  have hxsrc : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hatgt : a ∈ c.target := c.map_source hxsrc
  have hcax : c x₀ = a := ha.symm
  -- `c.symm` tends to `x₀` at `a`, so eventually its values lie in `V`, in `Ω` and in the chart
  -- target
  have htend : Tendsto c.symm (𝓝 a) (𝓝 x₀) := c.tendsto_symm hxsrc
  have hnb : ∀ᶠ w in 𝓝 a, c.symm w ∈ V ∧ c.symm w ∈ Ω ∧ w ∈ c.target := by
    filter_upwards [htend.eventually hV, htend.eventually (hΩo.mem_nhds hx₀),
      c.open_target.mem_nhds hatgt] with w h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff.mp hnb
  -- the two-sided linear growth bound of `g = Φ ∘ c.symm` at `a`
  have hup : ∀ w ∈ Metric.ball a ε, w ≠ a → ‖(Φ ∘ c.symm) w‖ ≤ Real.exp C * ‖w - a‖ := by
    intro w hw hwne
    obtain ⟨hVw, hΩw, htw⟩ := hεsub (Metric.mem_ball.mp hw)
    have hcsw : c (c.symm w) = w := c.right_inv htw
    have hxne : c.symm w ≠ x₀ := by
      intro hcon
      apply hwne
      rw [← hcsw, hcon, hcax]
    have hbnd : |E (c.symm w) + Real.log ‖c (c.symm w) - c x₀‖| ≤ C :=
      hVbnd (c.symm w) hVw hΩw hxne
    have hbnd' : |E (c.symm w) + Real.log ‖w - a‖| ≤ C := by
      simpa only [hcsw, hcax] using hbnd
    have hr : 0 < ‖w - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwne)
    have h := (Work.Modulus.exp_bounds_of_abs_add_log hr hbnd').1
    have hmodw : ‖Φ (c.symm w)‖ = Real.exp (-(E (c.symm w))) := hmod (c.symm w) hΩw hxne
    simpa [Function.comp_apply, hmodw] using h
  have hlo : ∀ w ∈ Metric.ball a ε, w ≠ a → Real.exp (-C) * ‖w - a‖ ≤ ‖(Φ ∘ c.symm) w‖ := by
    intro w hw hwne
    obtain ⟨hVw, hΩw, htw⟩ := hεsub (Metric.mem_ball.mp hw)
    have hcsw : c (c.symm w) = w := c.right_inv htw
    have hxne : c.symm w ≠ x₀ := by
      intro hcon
      apply hwne
      rw [← hcsw, hcon, hcax]
    have hbnd : |E (c.symm w) + Real.log ‖c (c.symm w) - c x₀‖| ≤ C :=
      hVbnd (c.symm w) hVw hΩw hxne
    have hbnd' : |E (c.symm w) + Real.log ‖w - a‖| ≤ C := by
      simpa only [hcsw, hcax] using hbnd
    have hr : 0 < ‖w - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwne)
    have h := (Work.Modulus.exp_bounds_of_abs_add_log hr hbnd').2
    have hmodw : ‖Φ (c.symm w)‖ = Real.exp (-(E (c.symm w))) := hmod (c.symm w) hΩw hxne
    simpa [Function.comp_apply, hmodw] using h
  obtain ⟨F, hFana, hFne, hFeq⟩ :=
    Work.Modulus.simpleZeroOfGrowth hε (Real.exp_pos (-C)) hhol hup hlo
  exact ⟨F, hFana, hFne, hFeq⟩

end Work.SimplyConnected.ABS
