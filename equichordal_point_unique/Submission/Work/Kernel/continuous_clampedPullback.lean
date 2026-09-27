import Mathlib
import Submission.Work.Kernel.pairingPoleTools

namespace Work.Kernel

/-- **Continuity of a clamped chart pullback** (`hWc` of `Work.Drive.pairIntegrable_of_gradient_bounds`,
the remaining common prerequisite for every index of `hηI`, `hDI`, `hQI2` and the pole
integrability facts).

If `W` is supported in the chart ball of radius `s`, its chart representative is continuous on the
closed ball of radius `s`, and `s < σ`, then the clamped pullback at radius `σ` is continuous, i.e.
`Set.indicator (Metric.ball ((chartAt ℂ x) x) σ) (W ∘ (chartAt ℂ x).symm)` is continuous.

Where the `s < σ` matters: on `s ≤ dist w ((chartAt ℂ x) x) < σ` the chart is honest (`htgt` gives
`w ∈ (chartAt ℂ x).target`, so `(chartAt ℂ x) ((chartAt ℂ x).symm w) = w`, and `w` is outside the open
`s`-ball, so `(chartAt ℂ x).symm w ∉ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) s`, hence
outside `tsupport W` by `hsupp`) — so the chart representative vanishes on that whole closed annulus,
and the clamping introduces no jump at the `σ`-sphere.  This is the step that makes the `s i < σ i`
field of `Work.Kernel.GreenCover` earn its keep.

Suggested proof (**glue on `Metric.closedBall ((chartAt ℂ x) x) σ`, not on all of `ℂ`**: outside the
chart target the map `(chartAt ℂ x).symm` has junk values, so the chart representative is only
continuous where the chart is honest): the chart representative is continuous on
`closedBall ((chartAt ℂ x) x) s` by `hcont` and identically `0` on the closed annulus
`s ≤ dist · ((chartAt ℂ x) x) ≤ σ` by the paragraph above; these two closed sets cover
`closedBall ((chartAt ℂ x) x) σ` and agree on the sphere of radius `s` (both `0`), so the chart
representative is continuous on `closedBall ((chartAt ℂ x) x) σ`.  On that ball the clamped pullback
agrees with the chart representative on the open `σ`-ball and with `0` on the `σ`-sphere; off
`closedBall ((chartAt ℂ x) x) σ` it is identically `0`; hence continuity.  The reusable pieces are
`Work.Drive.clampedPullback_eq_zero_of_lt_dist` (the annulus/zero part, with the weaker hypothesis
`tsupport W ⊆ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) s`) and `Metric.ball_subset_closedBall`. -/
theorem continuous_clampedPullback {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    {x : X} {σ s : ℝ} {W : X → ℝ} (hsσ : s < σ)
    (htgt : Metric.ball ((chartAt ℂ x) x) σ ⊆ (chartAt ℂ x).target)
    (hcont : ContinuousOn (fun w : ℂ => W ((chartAt ℂ x).symm w))
      (Metric.closedBall ((chartAt ℂ x) x) s))
    (hsupp : tsupport W ⊆ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) s) :
    Continuous (Work.Drive.clampedPullback x σ W) := by
  -- On the whole closed annulus `s ≤ dist · ((chartAt ℂ x) x)` the chart representative vanishes:
  -- the point is in the chart target (as `dist · _ < σ`), the chart is honest there, and its
  -- preimage lies outside the chart ball of radius `s`, hence outside `tsupport W`.
  have hann : ∀ w : ℂ, s ≤ dist w ((chartAt ℂ x) x) → w ∈ Metric.ball ((chartAt ℂ x) x) σ →
      W ((chartAt ℂ x).symm w) = 0 := by
    intro w hws hwb
    have hwt : w ∈ (chartAt ℂ x).target := htgt hwb
    have hright : (chartAt ℂ x) ((chartAt ℂ x).symm w) = w := (chartAt ℂ x).right_inv hwt
    by_contra hne
    have hmem : (chartAt ℂ x).symm w ∈ tsupport W :=
      subset_tsupport W (Function.mem_support.mpr hne)
    have hch := hsupp hmem
    have hball : w ∈ Metric.ball ((chartAt ℂ x) x) s := by
      simpa only [Set.mem_preimage, hright] using hch.2
    rw [Metric.mem_ball] at hball
    exact absurd hball (not_lt.mpr hws)
  -- The clamped pullback agrees with the chart representative on the closed ball of radius `s`.
  have hC : ContinuousOn (Work.Drive.clampedPullback x σ W)
      (Metric.closedBall ((chartAt ℂ x) x) s) := by
    refine hcont.congr ?_
    intro w hw
    exact Work.Drive.clampedPullback_apply_of_mem (x₀ := x) (ρ := σ) (u := W)
      (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hsσ))
  -- and it vanishes on the closed set `{s ≤ dist · ((chartAt ℂ x) x)}`.
  have hD : ContinuousOn (Work.Drive.clampedPullback x σ W)
      {w : ℂ | s ≤ dist w ((chartAt ℂ x) x)} := by
    refine (continuousOn_const (c := (0 : ℝ))).congr ?_
    intro w hw
    by_cases hb : w ∈ Metric.ball ((chartAt ℂ x) x) σ
    · rw [Work.Drive.clampedPullback_apply_of_mem (x₀ := x) (ρ := σ) (u := W) hb]
      exact hann w hw hb
    · exact Work.Drive.clampedPullback_apply_of_notMem (x₀ := x) (ρ := σ) (u := W) hb
  -- these two closed sets cover the plane.
  have hcover : Metric.closedBall ((chartAt ℂ x) x) s ∪ {w : ℂ | s ≤ dist w ((chartAt ℂ x) x)}
      = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro w
    by_cases h : dist w ((chartAt ℂ x) x) < s
    · exact Or.inl (Metric.mem_closedBall.mpr h.le)
    · exact Or.inr (not_lt.mp h)
  have hunion : ContinuousOn (Work.Drive.clampedPullback x σ W)
      (Metric.closedBall ((chartAt ℂ x) x) s ∪ {w : ℂ | s ≤ dist w ((chartAt ℂ x) x)}) :=
    ContinuousOn.union_of_isClosed hC hD Metric.isClosed_closedBall
      (isClosed_le (f := fun _ : ℂ => s) (g := fun w : ℂ => dist w ((chartAt ℂ x) x))
        continuous_const (continuous_id.dist continuous_const))
  rw [hcover] at hunion
  exact continuousOn_univ.mp hunion

end Work.Kernel
