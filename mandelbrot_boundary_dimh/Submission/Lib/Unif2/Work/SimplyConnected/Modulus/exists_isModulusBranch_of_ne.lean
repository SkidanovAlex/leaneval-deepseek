import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusDefs

namespace Work.SimplyConnected.Modulus

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

open Filter Set

/-- **A local holomorphic branch of the modulus of a harmonic function.**  If `u` is harmonic at
`x`, then on a neighbourhood `U` of `x` there is a holomorphic, nowhere vanishing `Φ` with
`‖Φ y‖ = exp (-(u y))` for every `y ∈ U`: namely `Φ = exp (-(F + iF*))` for a local harmonic
conjugate `F` of `u`, which exists on a chart ball by
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`. -/
theorem exists_localBranch_of_harmonicOnXAt {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {u : X → ℝ} {x : X} (hu : Submission.HarmonicOnXAt u x) :
    ∃ (U : Set X) (Φ : X → ℂ), IsOpen U ∧ x ∈ U ∧ Submission.HolomorphicOnX Φ U ∧
      (∀ y ∈ U, Φ y ≠ 0) ∧ (∀ y ∈ U, ‖Φ y‖ = Real.exp (-(u y))) := by
  set c := chartAt ℂ x with hc
  have hxsrc : x ∈ c.source := mem_chart_source ℂ x
  rw [Submission.HarmonicOnXAt] at hu
  obtain ⟨R₁, hR₁, hR₁sub⟩ := Metric.mem_nhds_iff.mp
    ((InnerProductSpace.isOpen_setOfPred_harmonicAt (u ∘ c.symm)).mem_nhds hu)
  obtain ⟨R₂, hR₂, hR₂sub⟩ := Metric.mem_nhds_iff.mp
    (c.open_target.mem_nhds (c.map_source hxsrc))
  have hρ : 0 < min R₁ R₂ / 2 := by positivity
  have hρ₁ : min R₁ R₂ / 2 ≤ R₁ := by linarith [min_le_left R₁ R₂, hR₁]
  have hρ₂ : min R₁ R₂ / 2 ≤ R₂ := by linarith [min_le_right R₁ R₂, hR₂]
  have hharm' : InnerProductSpace.HarmonicOnNhd (u ∘ c.symm)
      (Metric.ball (c x) (min R₁ R₂ / 2)) :=
    fun w hw => hR₁sub (Metric.ball_subset_ball hρ₁ hw)
  obtain ⟨F₀, hF₀ana, hF₀re⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hharm'
  refine ⟨Submission.chartBall c (c x) (min R₁ R₂ / 2),
    fun y => Complex.exp (-(F₀ (c y))), Submission.chartBall_isOpen c (c x) _, ?_, ?_, ?_, ?_⟩
  · rw [Submission.mem_chartBall]
    exact ⟨hxsrc, Metric.mem_ball_self hρ⟩
  · intro y hy
    rw [Submission.mem_chartBall] at hy
    obtain ⟨hysrc, hyball⟩ := hy
    rw [Submission.HolomorphicOnXAt_iff_chart (f := fun y => Complex.exp (-(F₀ (c y))))
      (x := y) (y := x) hysrc]
    have hev : (fun y : X => Complex.exp (-(F₀ (c y)))) ∘ c.symm
        =ᶠ[𝓝 (c y)] (fun w : ℂ => Complex.exp (-(F₀ w))) := by
      filter_upwards [c.open_target.mem_nhds (c.map_source hysrc),
        Metric.isOpen_ball.mem_nhds hyball] with w hwt _
      simp only [Function.comp_apply]
      rw [c.right_inv hwt]
    exact (((hF₀ana (c y) hyball).neg).cexp).congr hev.symm
  · intro y _
    exact Complex.exp_ne_zero _
  · intro y hy
    rw [Submission.mem_chartBall] at hy
    obtain ⟨hysrc, hyball⟩ := hy
    have hre : (F₀ (c y)).re = u y := by
      have h := hF₀re hyball
      rw [Function.comp_apply, c.left_inv hysrc] at h
      exact h
    rw [Complex.norm_exp, Complex.neg_re, hre]

theorem exists_isModulusBranch_of_ne {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ x : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionE z₀ E) (hx : x ≠ z₀) :
    ∃ (U : Set X) (Φ : X → ℂ), Work.SC.IsModulusBranch z₀ E U Φ ∧ U ∈ nhds x ∧ Φ x ≠ 0 := by
  have hharm : Submission.HarmonicOnXAt E x := hE.1.2.1 x ⟨mem_univ x, hx⟩
  obtain ⟨U, Φ, hUopen, hxU, hΦhol, hΦne, hΦnorm⟩ :=
    exists_localBranch_of_harmonicOnXAt (X := X) hharm
  exact ⟨U, Φ, ⟨hUopen, hΦhol, fun y hy _ => hΦne y hy, fun y hy _ => hΦnorm y hy⟩,
    hUopen.mem_nhds hxU, hΦne x hxU⟩

end Work.SimplyConnected.Modulus
