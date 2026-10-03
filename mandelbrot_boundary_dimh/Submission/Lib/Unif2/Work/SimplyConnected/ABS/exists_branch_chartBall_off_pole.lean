import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusDefs
import Submission.Lib.Unif2.Work.SimplyConnected.Modulus.exists_isModulusBranch_of_ne
import Submission.Lib.Unif2.Work.Modulus.puncturedHarmonic

open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Harmonicity transports to an open subspace.**  A function harmonic on a set `S ⊆ X` at a
point `z` of an open subspace `U` (with `(z : X) ∈ S`) is harmonic at `z` when read on `U`: the
chart of `U` at `z` is the restriction of the ambient chart at `z`, so the two chart
representatives agree near the relevant point. -/
theorem harmonicOnXAt_restrict_opens {U : TopologicalSpace.Opens X} {u : X → ℝ} {S : Set X}
    (hu : Submission.HarmonicOnX u S) {z : U} (hz : (z : X) ∈ S) :
    Submission.HarmonicOnXAt (fun z : U => u z.1) z := by
  change InnerProductSpace.HarmonicAt
    ((fun z : U => u z.1) ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z)
  have hzat : InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ (z : X)).symm)
      ((chartAt ℂ (z : X)) (z : X)) := hu (z : X) hz
  have heq : ((fun z : U => u z.1) ∘ (chartAt ℂ z).symm)
      =ᶠ[nhds ((chartAt ℂ (z : X)) (z : X))] (u ∘ (chartAt ℂ (z : X)).symm) := by
    filter_upwards [(chartAt ℂ z).open_target.mem_nhds
      (Work.Modulus.opensChartAt_mem_target U z)] with w hw
    simp only [Function.comp_apply]
    rw [Work.Modulus.opensChartAt_symm_eqOn U z hw]
  rw [Work.Modulus.opensChartAt_apply U z]
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).mpr hzat

/-- **Chart balls form a neighbourhood basis.**  Around every point `x`, the chart balls
`chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ` for `ρ > 0` are a basis of neighbourhoods: the
inverse of the preferred chart at `x` is continuous at `(chartAt ℂ x) x`. -/
theorem exists_chartBall_subset_of_mem_nhds_sub {S : Set X} {x : X} (hS : S ∈ 𝓝 x) :
    ∃ ρ : ℝ, 0 < ρ ∧ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ ⊆ S := by
  have hsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hcont : Filter.Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x)) (𝓝 x) := by
    have h : Filter.Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x))
        (𝓝 ((chartAt ℂ x).symm ((chartAt ℂ x) x))) :=
      (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hsrc)
    rwa [(chartAt ℂ x).left_inv hsrc] at h
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hcont.eventually hS)
  refine ⟨ρ, hρ, ?_⟩
  intro y hy
  rw [Submission.mem_chartBall] at hy
  have h1 : (chartAt ℂ x).symm ((chartAt ℂ x) y) ∈ S := hρsub hy.2
  rwa [(chartAt ℂ x).left_inv hy.1] at h1

end Work.SimplyConnected.ABS

namespace Work.SimplyConnected.ABS

theorem exists_branch_chartBall_off_pole {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : TopologicalSpace.Opens X} {x₀ : X} (hx₀ : x₀ ∈ U) {E : X → ℝ}
    (hE : Work.SimplyConnected.ABS.IsGreenOn (U : Set X) x₀ E)
    {x : U} (hx : x ≠ (⟨x₀, hx₀⟩ : U)) :
    ∃ (ρ : ℝ) (Φ : U → ℂ), 0 < ρ ∧
      Work.SC.IsModulusBranch (⟨x₀, hx₀⟩ : U) (fun z : U => E z.1)
        (Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ) Φ ∧
      (∀ y ∈ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ,
        Φ y ≠ 0 ∨ Work.SC.chartDeriv Φ y ≠ 0) := by
  -- `E`, read on the open subspace `U`, is harmonic at `x` (which is not the pole)
  have hxS : (x : X) ∈ (U : Set X) \ {x₀} :=
    ⟨x.2, fun h => hx (Subtype.ext h)⟩
  have hharm : Submission.HarmonicOnXAt (fun z : U => E z.1) x :=
    harmonicOnXAt_restrict_opens (U := U) hE.2.1 hxS
  -- a local branch of the holomorphic modulus `exp (-E)` near `x`
  obtain ⟨V, Φ, hVo, hxV, hΦhol, hΦne, hΦnorm⟩ :=
    Work.SimplyConnected.Modulus.exists_localBranch_of_harmonicOnXAt hharm
  -- shrink its domain to a chart ball around `x`
  obtain ⟨ρ, hρ, hρsub⟩ := exists_chartBall_subset_of_mem_nhds_sub (hVo.mem_nhds hxV)
  refine ⟨ρ, Φ, hρ, ?_, ?_⟩
  · exact ⟨Submission.chartBall_isOpen (chartAt ℂ x) ((chartAt ℂ x) x) ρ,
      hΦhol.mono hρsub, fun y hy _ => hΦne y (hρsub hy),
      fun y hy _ => hΦnorm y (hρsub hy)⟩
  · intro y hy
    exact Or.inl (hΦne y (hρsub hy))

end Work.SimplyConnected.ABS
