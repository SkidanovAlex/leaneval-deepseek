import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.Analysis.Harmonic.integral_inner_gradient_eq_zero

/-!
# The chart-local Dirichlet pairing and the clamped chart pullback

Infrastructure for the "energy / Green identity" route to the symmetry of the Green function
(`Work.Drive.greenSymmetryLeRegion`).  See
`Submission/Work/Drive/NOTES_greenSymmetryLeRegion_energy_route.md`.

* `Work.Drive.clampedPullback c ρ u` — the chart pullback of `u`, clamped to the chart ball of
  radius `ρ` around the image of the base point (used to manufacture compactly supported,
  smooth test functions on `ℂ` out of functions on `X`).
* the regularity of the clamped pullback (smooth + compact support) when the support of `u` lies
  strictly inside a smaller chart ball,
* the chart-local integration by parts, `Work.Drive.integral_inner_gradient_eq_zero_local`:
  for `h` harmonic in a chart ball and a smooth compactly supported test function supported in it,
  the Dirichlet pairing of the clamped pullbacks vanishes.
-/

open MeasureTheory Classical
open scoped Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The chart pullback of `u`, clamped to the chart ball of radius `ρ` around the image of the base
point `x₀`.  On the ball this is `u ∘ (chartAt ℂ x₀).symm`; outside it is `0`. -/
def clampedPullback (x₀ : X) (ρ : ℝ) (u : X → ℝ) : ℂ → ℝ :=
  Set.indicator (Metric.ball ((chartAt ℂ x₀) x₀) ρ) (fun w : ℂ => u ((chartAt ℂ x₀).symm w))

@[simp] theorem clampedPullback_apply_of_mem {x₀ : X} {ρ : ℝ} {u : X → ℝ} {w : ℂ}
    (hw : w ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ) :
    clampedPullback x₀ ρ u w = u ((chartAt ℂ x₀).symm w) :=
  Set.indicator_of_mem hw _

@[simp] theorem clampedPullback_apply_of_notMem {x₀ : X} {ρ : ℝ} {u : X → ℝ} {w : ℂ}
    (hw : w ∉ Metric.ball ((chartAt ℂ x₀) x₀) ρ) : clampedPullback x₀ ρ u w = 0 :=
  Set.indicator_of_notMem hw _

/-- **Vanishing of the clamped pullback away from a smaller ball.**  If the support of `u` lies
inside the chart preimage of the ball of radius `ρ₀`, then the clamped pullback (clamped at the
larger radius `ρ > ρ₀`) vanishes at every point at distance more than `ρ₀` from the base point. -/
theorem clampedPullback_eq_zero_of_lt_dist {x₀ : X} {ρ ρ₀ : ℝ} {u : X → ℝ}
    (htgt : Metric.ball ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hsupp : tsupport u ⊆ (chartAt ℂ x₀) ⁻¹' (Metric.ball ((chartAt ℂ x₀) x₀) ρ₀))
    {w : ℂ} (hw : ρ₀ < dist w ((chartAt ℂ x₀) x₀)) : clampedPullback x₀ ρ u w = 0 := by
  rw [clampedPullback]
  by_cases hb : w ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ
  · rw [Set.indicator_of_mem hb]
    have hwsrc : (chartAt ℂ x₀).symm w ∈ (chartAt ℂ x₀).source := by
      have : (chartAt ℂ x₀).symm w = (chartAt ℂ x₀).symm w := rfl
      exact (chartAt ℂ x₀).map_target (htgt hb)
    by_contra hne
    have hmem : (chartAt ℂ x₀).symm w ∈ Function.support u := hne
    have : (chartAt ℂ x₀).symm w ∈ tsupport u := subset_tsupport _ hmem
    have := hsupp this
    rw [Set.mem_preimage] at this
    rw [(chartAt ℂ x₀).right_inv (htgt hb)] at this
    exact absurd this (not_lt.mpr hw.le)
  · exact Set.indicator_of_notMem hb _


/-- **Regularity of the clamped pullback.**  If `u` is real analytic in the preferred chart at `x₀`
and the support of `u` lies inside the chart preimage of the ball of radius `ρ₀ < ρ`, then the
clamped pullback of `u` (clamped at `ρ`) is real analytic on `ℂ` and has compact support. -/
theorem analyticOnNhd_clampedPullback_hasCompactSupport {x₀ : X} {u : X → ℝ} {ρ ρ₀ : ℝ}
    (hρ : 0 < ρ) (hρ₀ : 0 ≤ ρ₀) (hρ₀ρ : ρ₀ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hu : ∀ x ∈ (chartAt ℂ x₀).source, AnalyticAt ℝ (u ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x))
    (hsupp : tsupport u ⊆ (chartAt ℂ x₀) ⁻¹' (Metric.ball ((chartAt ℂ x₀) x₀) ρ₀)) :
    AnalyticOnNhd ℝ (clampedPullback x₀ ρ u) Set.univ ∧
      HasCompactSupport (clampedPullback x₀ ρ u) := by
  have hball : Metric.ball ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target := htgt
  have hzero : ∀ w : ℂ, ρ₀ < dist w ((chartAt ℂ x₀) x₀) → clampedPullback x₀ ρ u w = 0 :=
    fun w hw => clampedPullback_eq_zero_of_lt_dist htgt hsupp hw
  have hzero_ev : ∀ w : ℂ, ρ₀ < dist w ((chartAt ℂ x₀) x₀) →
      clampedPullback x₀ ρ u =ᶠ[𝓝 w] 0 := by
    intro w hw
    have hopen : IsOpen {z : ℂ | ρ₀ < dist z ((chartAt ℂ x₀) x₀)} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    filter_upwards [hopen.mem_nhds hw] with z hz
    exact hzero z hz
  constructor
  · intro w _
    by_cases hw : ρ₀ < dist w ((chartAt ℂ x₀) x₀)
    · exact (analyticAt_const (v := (0 : ℝ)) : AnalyticAt ℝ (fun _ : ℂ => (0 : ℝ)) w).congr (hzero_ev w hw).symm
    · push_neg at hw
      have hmem : w ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ := by
        rw [Metric.mem_ball]
        exact lt_of_le_of_lt hw hρ₀ρ
      have hsrc : (chartAt ℂ x₀).symm w ∈ (chartAt ℂ x₀).source :=
        (chartAt ℂ x₀).map_target (hball hmem)
      have hright : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm w) = w :=
        (chartAt ℂ x₀).right_inv (hball hmem)
      have hG : AnalyticAt ℝ (fun z : ℂ => u ((chartAt ℂ x₀).symm z)) w := by
        have := hu ((chartAt ℂ x₀).symm w) hsrc
        rwa [hright] at this
      refine hG.congr ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with z hz
      exact (clampedPullback_apply_of_mem hz).symm
  · rw [hasCompactSupport_def]
    refine IsCompact.of_isClosed_subset (isCompact_closedBall ((chartAt ℂ x₀) x₀) ρ)
      isClosed_closure (closure_minimal ?_ Metric.isClosed_closedBall)
    intro w hw
    by_contra hw'
    rw [Metric.mem_closedBall, not_le] at hw'
    exact hw (clampedPullback_eq_zero_of_lt_dist htgt hsupp (lt_trans hρ₀ρ hw'))


/-- **The chart-local integration by parts.**  `h` is harmonic in a chart ball of radius `ρ` around
`x₀`, and the smooth test function `φ` is supported inside the strictly smaller chart ball of radius
`ρ' < ρ₀ < ρ`.  Then the Dirichlet pairing of the clamped chart pullbacks vanishes. -/
theorem integral_inner_gradient_eq_zero_chartLocal [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {x₀ : X} {h φ : X → ℝ} {ρ ρ₀ ρ' : ℝ}
    (hρ' : 0 ≤ ρ') (hρ'ρ₀ : ρ' < ρ₀) (hρ₀ : 0 ≤ ρ₀) (hρ₀ρ : ρ₀ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hφan : ∀ x ∈ (chartAt ℂ x₀).source,
      AnalyticAt ℝ (φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x))
    (hφsupp : tsupport φ ⊆ (chartAt ℂ x₀) ⁻¹' (Metric.ball ((chartAt ℂ x₀) x₀) ρ'))
    (hhan : ∀ y ∈ (chartAt ℂ x₀) ⁻¹' (Metric.ball ((chartAt ℂ x₀) x₀) ρ),
      Submission.HarmonicOnXAt h y) :
    0 = ∫ (z : ℂ), inner (𝕜 := ℝ)
      (gradient (clampedPullback x₀ ρ h) z) (gradient (clampedPullback x₀ ρ φ) z) := by
  have hρpos : 0 < ρ := lt_of_le_of_lt hρ₀ hρ₀ρ
  obtain ⟨hφ_an, hφ_cs⟩ :=
    analyticOnNhd_clampedPullback_hasCompactSupport (x₀ := x₀) (u := φ)
      hρpos hρ' (lt_trans hρ'ρ₀ hρ₀ρ) htgt hφan hφsupp
  -- the support of the clamped pullback of `φ` is contained in the smaller ball
  have hsupp_clamped : Function.support (clampedPullback x₀ ρ φ) ⊆
      Metric.ball ((chartAt ℂ x₀) x₀) ρ' := by
    intro w hw
    rw [Function.mem_support] at hw
    by_cases hb : w ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ
    · rw [clampedPullback_apply_of_mem hb] at hw
      have hmem : (chartAt ℂ x₀).symm w ∈ tsupport φ :=
        subset_tsupport _ (Function.mem_support.mpr hw)
      have := hφsupp hmem
      rw [Set.mem_preimage] at this
      rwa [(chartAt ℂ x₀).right_inv (htgt hb)] at this
    · rw [clampedPullback_apply_of_notMem hb] at hw
      exact absurd rfl hw
  -- hence the topological support of the clamped pullback of `φ` lies in the ball of radius `ρ`
  have htsupp_clamped : tsupport (clampedPullback x₀ ρ φ) ⊆
      Metric.ball ((chartAt ℂ x₀) x₀) ρ := by
    have h1 : closure (Function.support (clampedPullback x₀ ρ φ)) ⊆
        Metric.closedBall ((chartAt ℂ x₀) x₀) ρ' :=
      closure_minimal (fun z hz => Metric.ball_subset_closedBall (hsupp_clamped hz))
        Metric.isClosed_closedBall
    have h2 : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ' ⊆
        Metric.ball ((chartAt ℂ x₀) x₀) ρ := by
      intro z hz
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt hz (lt_of_lt_of_le hρ'ρ₀ (le_of_lt hρ₀ρ))
    rw [tsupport]
    exact h1.trans h2
  -- harmonicity of the clamped pullback of `h` on the support of the test function
  have hh : ∀ w ∈ tsupport (clampedPullback x₀ ρ φ),
      InnerProductSpace.HarmonicAt (clampedPullback x₀ ρ h) w := by
    intro w hw
    have hwball : w ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ := htsupp_clamped hw
    have hsrc : (chartAt ℂ x₀).symm w ∈ (chartAt ℂ x₀).source :=
      (chartAt ℂ x₀).map_target (htgt hwball)
    have hright : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm w) = w :=
      (chartAt ℂ x₀).right_inv (htgt hwball)
    have hharm : Submission.HarmonicOnXAt h ((chartAt ℂ x₀).symm w) :=
      hhan ((chartAt ℂ x₀).symm w) (by rw [Set.mem_preimage, hright]; exact hwball)
    have hchart := (Submission.HarmonicOnXAt_iff_chart (X := X) (u := h)
      (x := (chartAt ℂ x₀).symm w) (y := x₀) hsrc).mp hharm
    rw [hright] at hchart
    have hev : (fun z : ℂ => h ((chartAt ℂ x₀).symm z)) =ᶠ[𝓝 w] clampedPullback x₀ ρ h := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hwball] with z hz
      exact (clampedPullback_apply_of_mem (x₀ := x₀) (ρ := ρ) (u := h) hz).symm
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp hchart
  exact (Work.Analysis.Harmonic.integral_inner_gradient_eq_zero
    (h := clampedPullback x₀ ρ h) (φ := clampedPullback x₀ ρ φ) hh hφ_an.contDiff hφ_cs).symm

end Work.Drive
