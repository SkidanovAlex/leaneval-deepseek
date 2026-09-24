import Mathlib
import Submission.Work.Modulus.Defs
import Submission.Work.Modulus.Hypothesis
import Submission.Work.Modulus.localPoleExpansion

/-!
# The local holomorphic modulus of a Green function

Let `X` be a connected complex one-manifold, `z₀ : X`, and `E : X → ℝ` a Green function with pole
`z₀` in the strong sense of `Submission.HasGreenFunctionE`.  This module proves that, on a small
chart ball around `z₀`, `E` is the logarithm of the modulus of a holomorphic function:

`∃ ρ > 0, ∃ Φ : X → ℂ, Φ` holomorphic on the chart ball of radius `ρ`, `Φ` has a simple zero at
`z₀`, and `‖Φ x‖ = exp (-(E x))` for `x ≠ z₀` in that ball.

The proof is the completely local one.  By `Work.Modulus.localPoleExpansion`, in the preferred
chart at `z₀` the Green function has the form
`E x = -log ‖c x - c z₀‖ + H (c x)` with `H` harmonic on a disc around `c z₀`.  A harmonic
function on a disc is the real part of a function `F` holomorphic on that disc
(`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`), and then
`Φ x = (c x - c z₀) · exp (-(F (c x)))` does the job: the prefactor supplies the simple zero at
`z₀` (equivalently the logarithmic pole of `E`), and
`‖Φ x‖ = ‖c x - c z₀‖ · exp (-H (c x)) = exp (log ‖c x - c z₀‖ - H (c x)) = exp (-(E x))`.

No global hypothesis is used: this is the building block out of which the global holomorphic
modulus of the chapter is assembled (`Work.Modulus.HasTrivialModulusMonodromy`).
-/

open scoped Topology

noncomputable section

open Filter Set

namespace Work.Modulus

theorem localHolomorphicModulus_of_unitGreen
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) :
    ∃ (ρ : ℝ) (Φ : X → ℂ), 0 < ρ ∧
      Submission.HolomorphicOnX Φ (Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ) ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      (∀ x ∈ Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ, x ≠ z₀ →
        ‖Φ x‖ = Real.exp (-(E x))) := by
  -- the local expansion of `E` at its pole
  obtain ⟨ρ₀, hρ₀, H, hHharm, hexp⟩ := localPoleExpansion hE
  -- a harmonic function on a disc is the real part of a holomorphic function on it
  obtain ⟨F, hFana, hFre⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f := H) hHharm
  set c := chartAt ℂ z₀ with hc
  set a : ℂ := c z₀ with ha
  have hsrc : z₀ ∈ c.source := mem_chart_source ℂ z₀
  have hatgt : a ∈ c.target := c.map_source hsrc
  have ha_ball : a ∈ Metric.ball a ρ₀ := by simp [Metric.mem_ball, hρ₀]
  -- the candidate holomorphic modulus
  set Φ : X → ℂ := fun x => (c x - a) * Complex.exp (-(F (c x))) with hΦ
  refine ⟨ρ₀ / 2, Φ, by linarith, ?_, ?_, ?_⟩
  · -- holomorphy on the chart ball
    intro x hx
    have hxsrc : x ∈ c.source := hx.1
    have hxball : c x ∈ Metric.ball a ρ₀ :=
      Metric.ball_subset_ball (by linarith) hx.2
    refine (Submission.HolomorphicOnXAt_iff_chart (f := Φ) (x := x) (y := z₀) hxsrc).mpr ?_
    have hev : (Φ ∘ c.symm) =ᶠ[𝓝 (c x)]
        (fun w : ℂ => (w - a) * Complex.exp (-(F w))) := by
      filter_upwards [c.open_target.mem_nhds (c.map_source hxsrc),
        Metric.isOpen_ball.mem_nhds hxball] with w hwt _hwb
      simp only [Function.comp_apply, hΦ]
      rw [c.right_inv hwt]
    refine (AnalyticAt.mul (analyticAt_id.sub analyticAt_const)
      (((hFana (c x) hxball).neg).cexp)).congr hev.symm
  · -- the logarithmic pole
    refine ⟨fun w : ℂ => Complex.exp (-(F w)), ?_, Complex.exp_ne_zero _, ?_⟩
    · exact ((hFana a ha_ball).neg).cexp
    · have hev : (Φ ∘ c.symm) =ᶠ[𝓝 a]
          (fun w : ℂ => (w - a) * Complex.exp (-(F w))) := by
        filter_upwards [c.open_target.mem_nhds hatgt, Metric.isOpen_ball.mem_nhds ha_ball]
          with w hwt _hwb
        simp only [Function.comp_apply, hΦ]
        rw [c.right_inv hwt]
      exact hev
  · -- the modulus
    intro x hx hxne
    have hxsrc : x ∈ c.source := hx.1
    have hxball : c x ∈ Metric.ball a ρ₀ := Metric.ball_subset_ball (by linarith) hx.2
    have hcxne : c x ≠ a := fun h => hxne (c.injOn hxsrc hsrc h)
    have hnf : ‖c x - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hcxne)
    have hfre : (F (c x)).re = H (c x) := hFre hxball
    have hnorm : ‖Φ x‖ = ‖c x - a‖ * Real.exp (-(H (c x))) := by
      simp only [hΦ, norm_mul, Complex.norm_exp, Complex.neg_re, hfre]
    rw [hnorm, hexp x ⟨hxsrc, hxball⟩ hxne]
    have hlog : Real.exp (Real.log ‖c x - a‖) = ‖c x - a‖ :=
      Real.exp_log (norm_pos_iff.mpr (sub_ne_zero.mpr hcxne))
    have harith : -( -Real.log ‖c x - a‖ + H (c x))
        = Real.log ‖c x - a‖ + (-(H (c x))) := by ring
    rw [harith, Real.exp_add, hlog]

/-- **Legacy form** of `localHolomorphicModulus_of_unitGreen` for the (unsatisfiable) predicate
`Submission.HasGreenFunctionE`, kept so that callers of the earlier interface still compile.  The
hypothesis is stronger than the mathematics needs; everything downstream of it is vacuously
true, and the chapter's native statement is the `_of_unitGreen` one. -/
theorem localHolomorphicModulus
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Submission.HasGreenFunctionE z₀ E) :
    ∃ (ρ : ℝ) (Φ : X → ℂ), 0 < ρ ∧
      Submission.HolomorphicOnX Φ (Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ) ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      (∀ x ∈ Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ, x ≠ z₀ →
        ‖Φ x‖ = Real.exp (-(E x))) :=
  localHolomorphicModulus_of_unitGreen (isUnitGreenFunctionAt_of_hasGreenFunctionE hE)

end Work.Modulus
