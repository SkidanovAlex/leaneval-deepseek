import Mathlib
import Submission.Work.L62.section_chain

namespace Work.L62

/-- **Translation of an inverse branch, and the geometry of its image.**
Let `ψ` be a differentiable right inverse of `F` over the disc `ball c₀ r` (`F (ψ z) = z`),
injective there, with values in `U`.  Then for every translation `c` and every radius `ρ` with
`ρ + ‖c‖ < r / 2`, the translated curve `ψ (· + c)` is a right inverse of `F · - c` over
`ball c₀ ρ`: its image `W = ψ '' ball (c₀ + c) ρ` is open, connected, bounded, mapped bijectively
onto `ball c₀ ρ` by `F · - c`, and contained in the compact set
`ψ '' closedBall c₀ (r / 2) ⊆ U`. -/
theorem branch_translate_image {F ψ : ℂ → ℂ} {c₀ c : ℂ} {r ρ : ℝ} {U : Set ℂ}
    (hr : 0 < r) (hρ : 0 < ρ) (hρc : ρ + ‖c‖ < r / 2)
    (hψd : DifferentiableOn ℂ ψ (Metric.ball c₀ r))
    (hψinv : ∀ z ∈ Metric.ball c₀ r, F (ψ z) = z)
    (hψmem : Set.MapsTo ψ (Metric.ball c₀ r) U)
    (hψinj : Set.InjOn ψ (Metric.ball c₀ r)) :
    IsOpen (ψ '' Metric.ball (c₀ + c) ρ) ∧
      IsConnected (ψ '' Metric.ball (c₀ + c) ρ) ∧
      (fun w => F w - c) '' (ψ '' Metric.ball (c₀ + c) ρ) = Metric.ball c₀ ρ ∧
      Set.InjOn (fun w => F w - c) (ψ '' Metric.ball (c₀ + c) ρ) ∧
      IsCompact (ψ '' Metric.closedBall c₀ (r / 2)) ∧
      ψ '' Metric.closedBall c₀ (r / 2) ⊆ U ∧
      ψ '' Metric.ball (c₀ + c) ρ ⊆ ψ '' Metric.closedBall c₀ (r / 2) ∧
      Bornology.IsBounded (ψ '' Metric.ball (c₀ + c) ρ) := by
  have hr2 : 0 < r / 2 := half_pos hr
  -- the translated disc sits well inside the disc of definition
  have hb_sub : Metric.ball (c₀ + c) ρ ⊆ Metric.ball c₀ r := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    calc ‖z - c₀‖ = ‖(z - (c₀ + c)) + c‖ := by congr 1; ring
      _ ≤ ‖z - (c₀ + c)‖ + ‖c‖ := norm_add_le _ _
      _ < ρ + ‖c‖ := by linarith
      _ < r / 2 := hρc
      _ < r := by linarith
  have hb_cb : Metric.ball (c₀ + c) ρ ⊆ Metric.closedBall c₀ (r / 2) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖z - c₀‖ = ‖(z - (c₀ + c)) + c‖ := by congr 1; ring
      _ ≤ ‖z - (c₀ + c)‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ρ + ‖c‖ := by linarith
      _ ≤ r / 2 := le_of_lt hρc
  have hcb_sub : Metric.closedBall c₀ (r / 2) ⊆ Metric.ball c₀ r := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  have hcont : ContinuousOn ψ (Metric.ball (c₀ + c) ρ) := (hψd.mono hb_sub).continuousOn
  -- openness: a nonconstant holomorphic function is an open map
  have hopen : IsOpen (ψ '' Metric.ball (c₀ + c) ρ) := by
    have hψan : AnalyticOnNhd ℂ ψ (Metric.ball c₀ r) := hψd.analyticOnNhd Metric.isOpen_ball
    have hpre : IsPreconnected (Metric.ball c₀ r) := (convex_ball c₀ r).isPreconnected
    rcases hψan.is_constant_or_isOpen hpre with ⟨w, hw⟩ | h2
    · exfalso
      have hz1 : c₀ ∈ Metric.ball c₀ r := Metric.mem_ball_self hr
      have hz2 : c₀ + ((r / 2 : ℝ) : ℂ) ∈ Metric.ball c₀ r := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        have hn : ‖((r / 2 : ℝ) : ℂ)‖ = |r| / 2 := by simp
        rw [hn, abs_of_pos hr]
        linarith
      have heq : ψ c₀ = ψ (c₀ + ((r / 2 : ℝ) : ℂ)) := by rw [hw c₀ hz1, hw _ hz2]
      have heqc : c₀ = c₀ + ((r / 2 : ℝ) : ℂ) := hψinj hz1 hz2 heq
      have hzero : ((r / 2 : ℝ) : ℂ) = 0 := by
        have h1 : c₀ + ((r / 2 : ℝ) : ℂ) - c₀ = 0 := sub_eq_zero.mpr heqc.symm
        simpa using h1
      exact (ne_of_gt hr2) (Complex.ofReal_eq_zero.mp hzero)
    · exact h2 _ hb_sub Metric.isOpen_ball
  -- connectedness: image of a ball under a continuous map
  have hconn : IsConnected (ψ '' Metric.ball (c₀ + c) ρ) :=
    (Metric.isConnected_ball (x := c₀ + c) hρ).image ψ hcont
  -- the translated branch is a bijection onto the target disc
  have himg : (fun w => F w - c) '' (ψ '' Metric.ball (c₀ + c) ρ) = Metric.ball c₀ ρ := by
    ext y
    constructor
    · rintro ⟨w, ⟨z, hz, rfl⟩, hy⟩
      rw [← hy]
      change F (ψ z) - c ∈ Metric.ball c₀ ρ
      rw [hψinv z (hb_sub hz)]
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      calc ‖z - c - c₀‖ = ‖z - (c₀ + c)‖ := by congr 1; ring
        _ < ρ := hz
    · intro hy
      have hyc : y + c ∈ Metric.ball (c₀ + c) ρ := by
        rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
        calc ‖y + c - (c₀ + c)‖ = ‖y - c₀‖ := by congr 1; ring
          _ < ρ := hy
      refine ⟨ψ (y + c), ⟨y + c, hyc, rfl⟩, ?_⟩
      change F (ψ (y + c)) - c = y
      rw [hψinv (y + c) (hb_sub hyc)]
      ring
  have hinj : Set.InjOn (fun w => F w - c) (ψ '' Metric.ball (c₀ + c) ρ) := by
    rintro w₁ ⟨z₁, hz₁, rfl⟩ w₂ ⟨z₂, hz₂, rfl⟩ h
    change F (ψ z₁) - c = F (ψ z₂) - c at h
    rw [hψinv z₁ (hb_sub hz₁), hψinv z₂ (hb_sub hz₂)] at h
    have hz : z₁ = z₂ := sub_left_inj.mp h
    rw [hz]
  have hcomp : IsCompact (ψ '' Metric.closedBall c₀ (r / 2)) :=
    (isCompact_closedBall c₀ (r / 2)).image_of_continuousOn (hψd.continuousOn.mono hcb_sub)
  have hmemU : ψ '' Metric.closedBall c₀ (r / 2) ⊆ U := by
    rintro y ⟨z, hz, rfl⟩
    exact hψmem (hcb_sub hz)
  exact ⟨hopen, hconn, himg, hinj, hcomp, hmemU, Set.image_mono hb_cb,
    hcomp.isBounded.subset (Set.image_mono hb_cb)⟩

end Work.L62
