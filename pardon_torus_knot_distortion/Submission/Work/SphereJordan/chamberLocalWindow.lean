import Mathlib
import Submission.Work.SphereJordan.chamberDefs
import Submission.Work.SphereJordan.exteriorGermSetup

/-!
# The trace component is open in the trace: a local window around each of its points

Let `γ` be a simple closed plane curve, `B = Metric.ball p ε` a ball, `a ∈ γ.trace ∩ B` and

`A := traceComponent γ p ε a = connectedComponentIn (γ.trace ∩ B) a`.

Any point `a'` of `A` is an interior point of the trace-arc `A`: there is a ball around `a'` in
which the trace is contained in `A`.  Equivalently `A` is open in the trace.

The proof parametrises the trace locally: by `exists_window` (`Work.SphereJordan.exteriorGermSetup`)
the trace inside a small ball around `a'` is covered by the image of a parameter window
`γ '' Icc (θ - δ) (θ + δ)` with `δ < π`, and this image is a preconnected subset of the trace which
lies in `B` (the window being shrunk so that its image is inside the ball, `exists_window_sub`) and
contains `a'`; hence it is contained in the component `A` of `a'`.
-/

namespace Work.SphereJordan

open Set Metric

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- A small parameter window around a trace point inside the ball maps into the ball. -/
theorem exists_window_sub {p : ℂ} {ε : ℝ} (hε : 0 < ε) {a : ℂ} (ha : a ∈ Metric.ball p ε)
    {θ₀ : ℝ} (hθ : γ.γ θ₀ = a) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi ∧ γ.γ '' Set.Icc (θ₀ - δ) (θ₀ + δ) ⊆ Metric.ball p ε := by
  have ha' : γ.γ θ₀ ∈ Metric.ball p ε := by rw [hθ]; exact ha
  have hdist : dist (γ.γ θ₀) p < ε := Metric.mem_ball.mp ha'
  have hcont : ContinuousAt γ.γ θ₀ := γ.cont.continuousAt
  obtain ⟨δ₁, hδ₁, hδ₁h⟩ := (Metric.continuousAt_iff.mp hcont) (ε - dist (γ.γ θ₀) p) (by linarith)
  refine ⟨min (δ₁/2) (Real.pi/2), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by positivity)
  · have hp := Real.pi_pos
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · rintro z ⟨t, ht, rfl⟩
    have hmin1 : min (δ₁/2) (Real.pi/2) ≤ δ₁/2 := min_le_left _ _
    have hmin2 : min (δ₁/2) (Real.pi/2) < δ₁ := lt_of_le_of_lt hmin1 (by linarith)
    have htclose : dist t θ₀ < δ₁ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1, hmin2], by linarith [ht.2, hmin2]⟩
    have h := hδ₁h htclose
    rw [dist_comm] at h
    rw [Metric.mem_ball, dist_comm]
    calc dist p (γ.γ t) ≤ dist p (γ.γ θ₀) + dist (γ.γ θ₀) (γ.γ t) := dist_triangle _ _ _
      _ < dist p (γ.γ θ₀) + (ε - dist (γ.γ θ₀) p) := by linarith [h]
      _ = ε := by rw [dist_comm p (γ.γ θ₀)]; ring

/-- **The trace component is open in the trace.**  Every point of `traceComponent γ p ε a` has a
ball around it in which the trace is contained in `traceComponent γ p ε a`. -/
theorem mem_traceComponent_open (hs : γ.IsSimple) {p : ℂ} {ε : ℝ} (hε : 0 < ε) {a : ℂ}
    (ha : a ∈ γ.trace ∩ Metric.ball p ε) {a' : ℂ} (ha' : a' ∈ traceComponent γ p ε a) :
    ∃ r : ℝ, 0 < r ∧ γ.trace ∩ Metric.ball a' r ⊆ traceComponent γ p ε a := by
  have ha'tr : a' ∈ γ.trace := (traceComponent_subset_trace γ p ε a) ha'
  have ha'ball : a' ∈ Metric.ball p ε := (traceComponent_subset_ball γ p ε a) ha'
  obtain ⟨θ₀, hθ⟩ : ∃ θ₀, γ.γ θ₀ = a' := ha'tr
  obtain ⟨δ, hδ, hδπ, hWsub⟩ := exists_window_sub (γ := γ) hε ha'ball hθ
  obtain ⟨ρ, hρ, hwin⟩ := exists_window (γ := γ) hs hδ hδπ
  refine ⟨ρ, hρ, ?_⟩
  intro z hz
  obtain ⟨hztr, hzball⟩ := hz
  obtain ⟨tz, htz⟩ : ∃ tz, γ.γ tz = z := hztr
  have hz' : ‖γ.γ tz - γ.γ θ₀‖ < ρ := by
    have h1 : dist z a' < ρ := Metric.mem_ball.mp hzball
    rw [← htz, ← hθ] at h1
    rwa [dist_eq_norm] at h1
  obtain ⟨s, hsI, hsz⟩ := hwin tz hz'
  have hzW : z ∈ γ.γ '' Set.Icc (θ₀ - δ) (θ₀ + δ) := ⟨s, hsI, hsz.trans htz⟩
  have hWtr : γ.γ '' Set.Icc (θ₀ - δ) (θ₀ + δ) ⊆ γ.trace := by
    rintro _ ⟨t, -, rfl⟩; exact γ.mem_trace t
  have hWpre : IsPreconnected (γ.γ '' Set.Icc (θ₀ - δ) (θ₀ + δ)) :=
    (convex_Icc _ _).isPreconnected.image _ γ.cont.continuousOn
  have ha'W : a' ∈ γ.γ '' Set.Icc (θ₀ - δ) (θ₀ + δ) := ⟨θ₀, ⟨by linarith, by linarith⟩, hθ⟩
  have hcomp : γ.γ '' Set.Icc (θ₀ - δ) (θ₀ + δ) ⊆ traceComponent γ p ε a' :=
    hWpre.subset_connectedComponentIn ha'W (fun w hw => ⟨hWtr hw, hWsub hw⟩)
  have heq : traceComponent γ p ε a' = traceComponent γ p ε a := by
    unfold traceComponent
    exact (connectedComponentIn_eq ha').symm
  rw [heq] at hcomp
  exact hcomp hzW


/-- **A local window with a trace point outside it.**  For a point `z` of the trace component `A`
(inside the ball, and with the trace not contained in the whole ball) there is a radius `r > 0` such
that the trace inside `Metric.ball z r` is contained in `A` *and* some trace point lies outside
`Metric.closedBall z r`.  This is the local setting in which
`Work.SphereJordan.exists_trace_crosscut` applies (`p := z`, `ε := r`), giving the local crosscut of
`A` through `z` without any tangency hypothesis at the level of the big ball. -/
theorem exists_local_window_off_ball {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple)
    {p : ℂ} {ε : ℝ} {a : ℂ} (ha : a ∈ γ.trace ∩ Metric.ball p ε)
    (hε : 0 < ε) (hnot : ¬ γ.trace ⊆ Metric.ball p ε)
    {z : ℂ} (hz : z ∈ traceComponent γ p ε a) :
    ∃ r : ℝ, 0 < r ∧ γ.trace ∩ Metric.ball z r ⊆ traceComponent γ p ε a ∧
      ∃ t : ℝ, γ.γ t ∉ Metric.closedBall z r := by
  obtain ⟨r₀, hr₀, hwin⟩ := mem_traceComponent_open (γ := γ) hs hε ha hz
  have hzball : z ∈ Metric.ball p ε := traceComponent_subset_ball γ p ε a hz
  have hzp : dist z p < ε := Metric.mem_ball.mp hzball
  obtain ⟨y, hyt, hyb⟩ := Set.not_subset.mp hnot
  obtain ⟨t₀, ht₀⟩ := hyt
  have ht₀ball : ε ≤ dist (γ.γ t₀) p := by
    rw [ht₀]
    exact not_lt.mp (fun h => hyb (Metric.mem_ball.mpr h))
  have hδ : 0 < ε - dist p z := by rw [sub_pos]; rwa [dist_comm] at hzp
  refine ⟨min r₀ ((ε - dist p z) / 2), lt_min hr₀ (by linarith), ?_, ?_⟩
  · exact fun w hw => hwin ⟨hw.1, Metric.ball_subset_ball (min_le_left _ _) hw.2⟩
  · refine ⟨t₀, ?_⟩
    rw [Metric.mem_closedBall, not_le]
    have h4 : ε - dist p z ≤ dist (γ.γ t₀) z := by
      have h2 : dist (γ.γ t₀) p ≤ dist (γ.γ t₀) z + dist z p := dist_triangle (γ.γ t₀) z p
      have h7 : dist z p = dist p z := dist_comm z p
      linarith
    calc min r₀ ((ε - dist p z) / 2) ≤ (ε - dist p z) / 2 := min_le_right _ _
      _ < dist (γ.γ t₀) z := by linarith

end

end Work.SphereJordan
