import Mathlib
import Submission.Work.OddBound.mountainPass.port.local_joinedIn_ball_of_negDefPlane

namespace Work.OddBound.mountainPass3

open scoped ContDiff Topology

/-- **Local path connectedness of a sublevel set at a critical point whose Hessian is negative
definite on a two-plane**, with `C²` assumed only on a ball.

If `f` is `C²` on `Metric.ball u R`, has vanishing derivative at `u`, and its second derivative at
`u` is negative definite on a two-plane, then for all sufficiently small `ρ` any two points of
`{f < f u}` within distance `ρ` of `u` can be joined by a path which stays in `{f < f u}` and
inside `Metric.ball u R`.

The proof localises `f` by multiplying it with a smooth bump function which is `1` near `u` and
supported well inside `Metric.ball u R`; the localised function is `C²` everywhere, agrees with `f`
near `u` (so has the same first and second derivatives there), and the (already proved) global
statement `Work.OddBound.mountainPass.port.local_joinedIn_ball_of_negDefPlane` applies to it. -/
theorem local_joinedIn_of_negDefPlane_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {u : E} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 2 f (Metric.ball u R)) (hcz : fderiv ℝ f u = 0)
    (hbad : ∃ v w : E, ∀ c d : ℝ, (c, d) ≠ 0 →
      (fderiv ℝ (fderiv ℝ f) u) (c • v + d • w) (c • v + d • w) < 0) :
    ∃ ρ > 0, ∀ x y : E, dist x u < ρ → dist y u < ρ → f x < f u → f y < f u →
      ∃ γ : ℝ → E, ContinuousOn γ unitInterval ∧ γ 0 = x ∧ γ 1 = y ∧
        (∀ t ∈ unitInterval, f (γ t) < f u) ∧ (∀ t ∈ unitInterval, dist (γ t) u < R) := by
  classical
  -- a smooth bump function which equals `1` near `u` and vanishes outside `Metric.ball u (R/2)`
  let b : ContDiffBump u := ⟨R / 4, R / 2, by linarith, by linarith⟩
  have hb_rIn : b.rIn = R / 4 := rfl
  have hb_rOut : b.rOut = R / 2 := rfl
  have hbp : (0 : ℝ) < b.rIn := b.rIn_pos
  -- the localisation `b * f`, which is `C²` everywhere and equals `f` near `u`
  set F : E → ℝ := fun w => b w * f w with hFdef
  have hF_eq : ∀ z : E, dist z u < b.rIn → F z = f z := by
    intro z hz
    have h1 : b z = 1 := b.one_of_mem_closedBall (by rw [Metric.mem_closedBall]; linarith)
    rw [hFdef]
    simp [h1]
  have hFu : F u = f u := hF_eq u (by rw [dist_self]; exact hbp)
  have hFdiff : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rw [hFdef]
    by_cases hx : x ∈ Metric.ball u R
    · exact ((b.contDiff (n := 2)).contDiffAt).mul
        (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hx))
    · -- far from `u` the bump function vanishes on a whole neighbourhood
      refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℝ))) ?_
      have hxR : R ≤ dist x u := by
        rw [Metric.mem_ball, not_lt] at hx
        exact hx
      have hxcl : x ∉ Metric.closedBall u b.rOut := by
        rw [Metric.mem_closedBall, not_le]
        linarith
      have hU : (Metric.closedBall u b.rOut)ᶜ ∈ 𝓝 x :=
        Metric.isClosed_closedBall.isOpen_compl.mem_nhds hxcl
      filter_upwards [hU] with z hz
      have hz2 : b.rOut ≤ dist z u := by
        rw [Set.mem_compl_iff, Metric.mem_closedBall] at hz
        exact le_of_lt (not_le.mp hz)
      rw [b.zero_of_le_dist hz2, zero_mul]
  -- the first and second derivatives of `F` at `u` agree with those of `f`
  have hFeq : F =ᶠ[𝓝 u] f := by
    filter_upwards [Metric.ball_mem_nhds u hbp] with z hz
    exact hF_eq z hz
  have hdF : fderiv ℝ F u = 0 := by rw [hFeq.fderiv_eq, hcz]
  have hFeq' : fderiv ℝ F =ᶠ[𝓝 u] fderiv ℝ f := by
    filter_upwards [Metric.ball_mem_nhds u hbp] with z hz
    have hloc : F =ᶠ[𝓝 z] f :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) (fun w hw => hF_eq w hw)
    exact hloc.fderiv_eq
  have hHess : fderiv ℝ (fderiv ℝ F) u = fderiv ℝ (fderiv ℝ f) u := hFeq'.fderiv_eq
  have hbadF : ∃ v w : E, ∀ c d : ℝ, (c, d) ≠ 0 →
      (fderiv ℝ (fderiv ℝ F) u) (c • v + d • w) (c • v + d • w) < 0 := by
    obtain ⟨v, w, hv⟩ := hbad
    exact ⟨v, w, fun c d hcd => by rw [hHess]; exact hv c d hcd⟩
  -- apply the global statement to the localised function
  obtain ⟨ρ₀, hρ₀, hpath⟩ :=
    Work.OddBound.mountainPass.port.local_joinedIn_ball_of_negDefPlane
      (F := F) hFdiff hFu hdF hbadF b.rIn hbp
  refine ⟨min ρ₀ b.rIn, lt_min hρ₀ hbp, fun x y hx hy hfx hfy => ?_⟩
  have hx₁ : dist x u < ρ₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hy₁ : dist y u < ρ₀ := lt_of_lt_of_le hy (min_le_left _ _)
  have hx₂ : dist x u < b.rIn := lt_of_lt_of_le hx (min_le_right _ _)
  have hy₂ : dist y u < b.rIn := lt_of_lt_of_le hy (min_le_right _ _)
  have hj : JoinedIn ({w : E | F w < f u} ∩ Metric.ball u b.rIn) x y :=
    hpath x y hx₁ hy₁ (by rw [hF_eq x hx₂]; exact hfx) (by rw [hF_eq y hy₂]; exact hfy)
  obtain ⟨p, hp⟩ := hj
  have hmain : ∀ t ∈ unitInterval, f (p.extend t) < f u := by
    intro t ht
    have h1 : F (p ⟨t, ht⟩) < f u := (hp ⟨t, ht⟩).1
    have h2 : dist (p ⟨t, ht⟩) u < b.rIn := (hp ⟨t, ht⟩).2
    rw [Path.extend_apply p ht, ← hF_eq (p ⟨t, ht⟩) h2]
    exact h1
  have hdist : ∀ t ∈ unitInterval, dist (p.extend t) u < R := by
    intro t ht
    have h2 : dist (p ⟨t, ht⟩) u < b.rIn := (hp ⟨t, ht⟩).2
    rw [hb_rIn] at h2
    rw [Path.extend_apply p ht]
    linarith
  exact ⟨fun t => p.extend t, p.continuous_extend.continuousOn,
    Path.extend_zero p, Path.extend_one p, hmain, hdist⟩

end Work.OddBound.mountainPass3
