import Mathlib
import Submission.RiemannSurface
import Submission.Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue

/-!
# The zero extension of a nonnegative harmonic function is subharmonic

**Robbin, *The Uniformization Theorem*, Corollary 2.2 (iv).**  If `u : X → ℝ` is continuous,
nonnegative, harmonic on an open set `U`, and vanishes outside `U`, then `u` is subharmonic on all
of `X`.

This turns "a positive harmonic function vanishing at the boundary of its domain" into a *barrier*
for the Perron/balayage constructions (it is the general form of the subharmonicity of
`Submission.chartLogClamp`, done by hand in `Submission/ChartLogClamp.lean`); Robbin's §4 uses it to
conclude that `1 - lim v_n`, extended by zero, is subharmonic.

Route: subharmonicity at `x` is `SubharmonicAtChart u (chartAt ℂ x) x`, whose mean-value content is
the circle inequality for the chart pullback.  That inequality is checked *locally* on the chart
ball — equality where `u` is harmonic, nonnegativity of the average where `u = 0` — and upgraded to
all circles by `Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue`.
-/

open Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The zero extension of a nonnegative harmonic function is subharmonic** (Robbin, Cor. 2.2
(iv)). -/
theorem SubharmonicOnX.of_nonneg_harmonic_zeroExtension {U : Set X} {u : X → ℝ}
    (hUo : IsOpen U) (hcont : Continuous u) (hnn : ∀ x, 0 ≤ u x)
    (hzero : ∀ x ∉ U, u x = 0) (hharm : Submission.HarmonicOnX u U) :
    Submission.SubharmonicOnX u Set.univ := by
  refine ⟨hcont.continuousOn, fun p _ => ?_⟩
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hc
  set v : ℂ → ℝ := fun z => u (c.symm z) with hv
  -- a chart ball around `p`, with its closure inside the chart target
  obtain ⟨ρ, hρ, hρball⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (c p) ρ ⊆ c.target := by
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp
      (c.open_target.mem_nhds (c.map_source (mem_chart_source ℂ p)))
    have hb : Metric.ball (c p) (ρ / 2) ⊆ Metric.ball (c p) ρ := Metric.ball_subset_ball (by linarith)
    exact ⟨ρ / 2, by linarith, hb.trans hsub⟩
  have hpsrc : p ∈ c.source := mem_chart_source ℂ p
  have hcontv : ContinuousOn v (Metric.ball (c p) ρ) :=
    hcont.comp_continuousOn (c.continuousOn_symm.mono (fun z hz => hρball hz))
  refine ⟨hpsrc, ρ, hρ, hρball, hcontv, ?_⟩
  -- the local circle mean-value inequality for the pullback
  have hloc : ∀ q ∈ Metric.ball (c p) ρ, ∃ ε : ℝ, 0 < ε ∧
      Metric.ball q ε ⊆ Metric.ball (c p) ρ ∧
      ∀ r : ℝ, 0 < r → Metric.closedBall q r ⊆ Metric.ball q ε →
        v q ≤ Real.circleAverage v q r := by
    intro q hq
    have hρq : 0 < ρ - dist q (c p) := by
      have h := Metric.mem_ball.mp hq
      rw [dist_eq_norm] at h ⊢
      linarith
    have hslack : ∀ z : ℂ, dist z q < ρ - dist q (c p) → dist z (c p) < ρ := by
      intro z hz
      have h1 : dist z (c p) ≤ dist z q + dist q (c p) := dist_triangle _ _ _
      have h2 : dist z q + dist q (c p) < ρ := by linarith
      exact lt_of_le_of_lt h1 h2
    by_cases hqU : c.symm q ∈ U
    · -- `u` is harmonic at `c.symm q`, so `v` is harmonic at `q`: equality
      have hcs : c (c.symm q) = q := c.right_inv (hρball hq)
      have hqsrc : c.symm q ∈ c.source := c.map_target (hρball hq)
      have hAt : InnerProductSpace.HarmonicAt v q := by
        have h1 : Submission.HarmonicOnXAt u (c.symm q) := hharm _ hqU
        have h2 := (Submission.HarmonicOnXAt_iff_chart (u := u) (x := c.symm q) (y := p)
          hqsrc).mp h1
        rwa [hcs] at h2
      obtain ⟨ε₀, hε₀, hε₀harm⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧
          ∀ y : ℂ, dist y q < ε₀ → InnerProductSpace.HarmonicAt v y := by
        obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp hAt.eventually
        exact ⟨ε₀, hε₀, fun y hy => hball (Metric.mem_ball.mpr hy)⟩
      exact ⟨min ε₀ (ρ - dist q (c p)), lt_min hε₀ hρq,
        fun z hz => Metric.mem_ball.mpr (hslack z (lt_of_lt_of_le (Metric.mem_ball.mp hz)
          (min_le_right _ _))),
        fun r hr hqr => by
          have hcl : Metric.closedBall q r ⊆ Metric.ball q ε₀ :=
            hqr.trans (Metric.ball_subset_ball (min_le_left _ _))
          have hnhd : InnerProductSpace.HarmonicOnNhd v (Metric.closedBall q |r|) := by
            rw [abs_of_pos hr]
            exact fun z hz => hε₀harm z (Metric.mem_ball.mp (hcl hz))
          rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq hnhd]⟩
    · -- `v q = 0` and the average is nonnegative
      have hvq : v q = 0 := by
        simp only [hv]
        exact hzero (c.symm q) hqU
      exact ⟨ρ - dist q (c p), hρq,
        fun z hz => Metric.mem_ball.mpr (hslack z (Metric.mem_ball.mp hz)),
        fun r hr hqr => by
          rw [hvq]
          have hcont_sphere : ContinuousOn v (Metric.sphere q |r|) := by
            rw [abs_of_pos hr]
            exact hcontv.mono (fun z hz => Metric.mem_ball.mpr
              (hslack z (Metric.mem_ball.mp (hqr (Metric.sphere_subset_closedBall hz)))))
          have hmono : Real.circleAverage (fun _ : ℂ => (0 : ℝ)) q r ≤
              Real.circleAverage v q r :=
            Real.circleAverage_mono (ContinuousOn.circleIntegrable' continuousOn_const)
              (ContinuousOn.circleIntegrable' hcont_sphere) (fun z _ => hnn (c.symm z))
          rwa [Real.circleAverage_const] at hmono⟩
  intro q hq r hr hqr
  exact Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue
    (Ω := Metric.ball (c p) ρ) Metric.isOpen_ball hcontv hloc q hq r hr hqr

end Work.Drive
