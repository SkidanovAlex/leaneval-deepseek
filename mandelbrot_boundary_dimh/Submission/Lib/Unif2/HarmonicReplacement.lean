import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.Perron
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue

/-!
# The harmonic replacement of a subharmonic function is subharmonic

Hubbard's construction of a Perron family (Definition 1.2.2) requires that the harmonic replacement
of a member in a disc again be subharmonic (and hence, for a Perron family, again a member).  This
module proves that the function which agrees with a subharmonic `f` outside a chart disc and with a
harmonic `u` inside it is subharmonic everywhere.

The only input from the Euclidean theory is the equivalence between the circle mean-value inequality
and its *local* form, `circleAverage_ge_of_localSubMeanValue`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section Basic

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Outside the chart disc the replacement agrees with the original function. -/
theorem replaceOnDisc_pullback_of_not_mem {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    {u : ℂ → ℝ} {f : X → ℝ} {z : ℂ} (hz : c.symm z ∉ chartBall c a ρ) :
    replaceOnDisc c a ρ u f (c.symm z) = f (c.symm z) :=
  replaceOnDisc_of_not_mem_chartBall hz

end Basic

section ReplacementSubharmonic

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The harmonic replacement of a subharmonic function is subharmonic.** -/
theorem replaceOnDisc_subharmonic {z₀ : X} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall a ρ ⊆ (chartAt ℂ z₀).target) {f : X → ℝ}
    (hf : SubharmonicOnX f univ) {u : ℂ → ℝ}
    (hu : ∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt u z)
    (hG : ContinuousOn (gluedBall u (fun w => f ((chartAt ℂ z₀).symm w)) a ρ)
      (Metric.closedBall a ρ)) :
    SubharmonicOnX (replaceOnDisc (chartAt ℂ z₀) a ρ u f) univ := by
  have hball : Metric.ball a ρ ⊆ (chartAt ℂ z₀).target :=
    fun z hz => hsub (Metric.ball_subset_closedBall hz)
  have hfcont : Continuous f := continuousOn_univ.mp hf.1
  have hucont : ContinuousOn u (Metric.ball a ρ) :=
    continuousOn_of_forall_continuousAt fun z hz =>
      (hu z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)).1.continuousAt
  have hgcont : Continuous (replaceOnDisc (chartAt ℂ z₀) a ρ u f) :=
    continuous_replaceOnDisc hsub hfcont hucont hG
  have hge : ∀ y : X, f y ≤ replaceOnDisc (chartAt ℂ z₀) a ρ u f y :=
    le_replaceOnDisc hf hρ hsub hu hG
  refine ⟨hgcont.continuousOn, ?_⟩
  intro x _
  by_cases hxc : x ∈ chartClosedBall (chartAt ℂ z₀) a ρ
  · -- near the disc: measure everything in the chart at `z₀`
    have hxs : x ∈ (chartAt ℂ z₀).source := chartClosedBall_subset_source _ _ _ hxc
    refine (SubharmonicOnXAt_iff_chartAt hxs).mpr ?_
    have hfchart : SubharmonicAtChart f (chartAt ℂ z₀) x :=
      SubharmonicOnX.subharmonicAtChart hf (mem_univ x) hxs
    rw [SubharmonicAtChart] at hfchart
    obtain ⟨-, ρf, hρf, htf, hcf, hmf⟩ := hfchart
    have hcontg : ContinuousOn
        (fun w : ℂ => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w))
        (Metric.ball ((chartAt ℂ z₀) x) ρf) :=
      hgcont.continuousOn.comp ((chartAt ℂ z₀).continuousOn_symm.mono htf) (fun z _ => mem_univ _)
    refine ⟨hxs, ρf, hρf, htf, hcontg, ?_⟩
    refine Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue
      Metric.isOpen_ball hcontg ?_
    intro q hq
    have hqt : q ∈ (chartAt ℂ z₀).target := htf hq
    have hqd : dist q ((chartAt ℂ z₀) x) < ρf := Metric.mem_ball.mp hq
    by_cases hqball : q ∈ Metric.ball a ρ
    · -- inside the replacement disc the replacement is harmonic
      have hqa : dist q a < ρ := Metric.mem_ball.mp hqball
      refine ⟨min (ρ - dist q a) (ρf - dist q ((chartAt ℂ z₀) x)),
        lt_min (by linarith) (by linarith),
        (Metric.ball_subset_ball (min_le_right _ _)).trans (ball_subset_ball_of_mem hq), ?_⟩
      intro r hr hpr
      have h1 : Metric.closedBall q r ⊆ Metric.ball a ρ :=
        (hpr.trans (Metric.ball_subset_ball (min_le_left _ _))).trans (ball_subset_ball_of_mem hqball)
      have h2 : Metric.closedBall q r ⊆ Metric.ball ((chartAt ℂ z₀) x) ρf :=
        (hpr.trans (Metric.ball_subset_ball (min_le_right _ _))).trans (ball_subset_ball_of_mem hq)
      have heqOn : ∀ z ∈ Metric.closedBall q r,
          replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm z) = u z :=
        fun z hz => replaceOnDisc_pullback_of_mem hball (h1 hz)
      have hqeq : replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q) = u q :=
        heqOn q (Metric.mem_closedBall_self (le_of_lt hr))
      have havg : Real.circleAverage
          (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r
          = Real.circleAverage u q r :=
        Real.circleAverage_congr_sphere (fun z hz => heqOn z (Metric.sphere_subset_closedBall
          (by simpa [abs_of_pos hr] using hz)))
      change replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q) ≤
        Real.circleAverage
          (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r
      rw [hqeq, havg]
      exact (InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by
        rw [abs_of_pos hr]
        intro z hz
        exact hu z (by simpa [Metric.mem_ball, dist_eq_norm] using h1 hz))).ge
    · by_cases hqsph : q ∈ Metric.sphere a ρ
      · -- on the boundary circle: the replacement dominates `f` and agrees with it at `q`
        refine ⟨ρf - dist q ((chartAt ℂ z₀) x), by linarith, ball_subset_ball_of_mem hq, ?_⟩
        intro r hr hpr
        have h2 : Metric.closedBall q r ⊆ Metric.ball ((chartAt ℂ z₀) x) ρf :=
          hpr.trans (ball_subset_ball_of_mem hq)
        have hqmem : replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q)
            = f ((chartAt ℂ z₀).symm q) := by
          refine replaceOnDisc_of_not_mem_chartBall ?_
          intro hmem
          exact hqball (by simpa [(chartAt ℂ z₀).right_inv hqt] using hmem.2)
        have hfmvp : (fun w => f ((chartAt ℂ z₀).symm w)) q
            ≤ Real.circleAverage (fun w => f ((chartAt ℂ z₀).symm w)) q r := hmf q hq r hr h2
        have hsphere' : Metric.sphere q r ⊆ Metric.ball ((chartAt ℂ z₀) x) ρf :=
          fun z hz => h2 (Metric.sphere_subset_closedBall hz)
        have hsphere'' : Metric.sphere q |r| ⊆ Metric.ball ((chartAt ℂ z₀) x) ρf :=
          fun z hz => h2 (Metric.sphere_subset_closedBall (by simpa [abs_of_pos hr] using hz))
        have hIf : CircleIntegrable (fun w => f ((chartAt ℂ z₀).symm w)) q r :=
          (hcf.mono hsphere').circleIntegrable (le_of_lt hr)
        have hIg : CircleIntegrable
            (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r :=
          (hcontg.mono hsphere').circleIntegrable (le_of_lt hr)
        have hm := Real.circleAverage_mono hIf hIg
          (fun z hz => hge ((chartAt ℂ z₀).symm z))
        change replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q) ≤
          Real.circleAverage
            (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r
        calc replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q)
            = f ((chartAt ℂ z₀).symm q) := hqmem
          _ ≤ Real.circleAverage (fun w => f ((chartAt ℂ z₀).symm w)) q r := hfmvp
          _ ≤ Real.circleAverage
              (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r := hm
      · -- outside the closed disc the replacement agrees with `f` near `q`
        have hqcl : q ∉ Metric.closedBall a ρ := by
          intro h
          rcases (Metric.mem_closedBall.mp h).lt_or_eq with hlt | heq
          · exact hqball (Metric.mem_ball.mpr hlt)
          · exact hqsph (Metric.mem_sphere.mpr heq)
        have hnbhd : (Metric.closedBall a ρ)ᶜ ∈ 𝓝 q :=
          (isOpen_compl_iff.mpr (Metric.isClosed_closedBall (x := a) (ε := ρ))).mem_nhds hqcl
        obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp hnbhd
        refine ⟨min ε₁ (ρf - dist q ((chartAt ℂ z₀) x)), lt_min hε₁ (by linarith),
          (Metric.ball_subset_ball (min_le_right _ _)).trans (ball_subset_ball_of_mem hq), ?_⟩
        intro r hr hpr
        have h2 : Metric.closedBall q r ⊆ Metric.ball ((chartAt ℂ z₀) x) ρf :=
          (hpr.trans (Metric.ball_subset_ball (min_le_right _ _))).trans (ball_subset_ball_of_mem hq)
        have hout : Metric.closedBall q r ⊆ (Metric.closedBall a ρ)ᶜ :=
          (hpr.trans (Metric.ball_subset_ball (min_le_left _ _))).trans hε₁sub
        have heqOn : ∀ z ∈ Metric.closedBall q r,
            replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm z)
              = f ((chartAt ℂ z₀).symm z) := by
          intro z hz
          have hzt : z ∈ (chartAt ℂ z₀).target := htf (h2 hz)
          refine replaceOnDisc_of_not_mem_chartBall ?_
          intro hmem
          refine hout hz ?_
          have h1 : z ∈ Metric.ball a ρ := by
            have h2' := hmem.2
            simp only [Set.mem_preimage] at h2'
            rwa [(chartAt ℂ z₀).right_inv hzt] at h2'
          exact Metric.ball_subset_closedBall h1
        have hqeq : replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q)
            = f ((chartAt ℂ z₀).symm q) := heqOn q (Metric.mem_closedBall_self (le_of_lt hr))
        have havg : Real.circleAverage
            (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r
            = Real.circleAverage (fun w => f ((chartAt ℂ z₀).symm w)) q r :=
          Real.circleAverage_congr_sphere (fun z hz => heqOn z (Metric.sphere_subset_closedBall
            (by simpa [abs_of_pos hr] using hz)))
        change replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q) ≤
          Real.circleAverage
            (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r
        rw [hqeq, havg]
        exact hmf q hq r hr h2
  · -- far from the disc: the replacement equals `f` on a neighbourhood of `x`
    have hne : (chartClosedBall (chartAt ℂ z₀) a ρ)ᶜ ∈ 𝓝 x :=
      (isClosed_chartClosedBall hsub).isOpen_compl.mem_nhds hxc
    have heq : f =ᶠ[𝓝 x] replaceOnDisc (chartAt ℂ z₀) a ρ u f := by
      filter_upwards [hne] with y hy
      exact (replaceOnDisc_of_not_mem_chartBall
        (fun hmem => hy (chartBall_subset_chartClosedBall _ _ _ hmem))).symm
    exact SubharmonicOnXAt.congr (hf.2 x (mem_univ x)) heq

end ReplacementSubharmonic

end Submission
