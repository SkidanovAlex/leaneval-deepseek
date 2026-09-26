import Mathlib
import Submission.Work.Asymptotics.residue_rectangle

set_option linter.unusedSimpArgs false

namespace Work.Asymptotics

open Complex MeasureTheory intervalIntegral Filter Topology Set

/-- The `re`/`im` coordinates of a point of a ball. -/
lemma abs_re_sub_lt_of_mem_ball {z w : ℂ} {ρ : ℝ} (hz : z ∈ Metric.ball w ρ) :
    |z.re - w.re| < ρ ∧ |z.im - w.im| < ρ := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  constructor
  · have h := Complex.abs_re_le_norm (z - w)
    rw [Complex.sub_re] at h
    exact lt_of_le_of_lt h hz
  · have h := Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_im] at h
    exact lt_of_le_of_lt h hz

/-- **Residue theorem for a rectangle, with a bounded remainder.**

This is `Work.Asymptotics.residue_rectangle` with the removable-singularity hypothesis
`DifferentiableAt ℂ (fun z => f z - c/(z - z₀)) z₀` replaced by the *weaker* hypothesis that the
remainder `f z - c/(z-z₀)` is bounded on a punctured neighbourhood of `z₀` — which is what the
residue calculus of the CKMRV kernels produces.  The two are equivalent by Riemann's removable
singularity theorem (`Complex.differentiableOn_update_limUnder_of_bddAbove`): the bounded
remainder `g` extends holomorphically across `z₀`, and `residue_rectangle` applies to the
extension (whose values off `z₀` — hence on the four edges — agree with `f`). -/
theorem residue_rectangle_of_bdd (f : ℂ → ℂ) (z₀ c : ℂ) (x₁ x₂ y₁ y₂ : ℝ)
    (hx₁ : x₁ < z₀.re) (hx₂ : z₀.re < x₂) (hy₁ : y₁ < z₀.im) (hy₂ : z₀.im < y₂)
    (hcont : ContinuousOn f
      ({z : ℂ | x₁ ≤ z.re ∧ z.re ≤ x₂ ∧ y₁ ≤ z.im ∧ z.im ≤ y₂} \ {z₀}))
    (hhol : ∀ z : ℂ, x₁ < z.re → z.re < x₂ → y₁ < z.im → z.im < y₂ → z ≠ z₀ →
      DifferentiableAt ℂ f z)
    (hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, z ≠ z₀ → ‖z - z₀‖ < r →
      ‖f z - c / (z - z₀)‖ ≤ M) :
    (∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I))
      - (∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₂ : ℂ) * Complex.I))
      + Complex.I * (∫ y : ℝ in y₁..y₂, f ((x₂ : ℂ) + (y : ℂ) * Complex.I))
      - Complex.I * (∫ y : ℝ in y₁..y₂, f ((x₁ : ℂ) + (y : ℂ) * Complex.I))
      = 2 * (Real.pi : ℂ) * Complex.I * c := by
  obtain ⟨M, hM0, r, hr0, hrM⟩ := hbdd
  -- a radius small enough to stay inside the rectangle and inside `r`
  set ρ : ℝ := min r (min (z₀.re - x₁) (min (x₂ - z₀.re) (min (z₀.im - y₁) (y₂ - z₀.im))))
  have hρr : ρ ≤ r := min_le_left _ _
  have hρre₁ : ρ ≤ z₀.re - x₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρre₂ : ρ ≤ x₂ - z₀.re :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρim₁ : ρ ≤ z₀.im - y₁ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_left _ _)))
  have hρim₂ : ρ ≤ y₂ - z₀.im :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_right _ _)))
  have hρ0 : 0 < ρ :=
    lt_min hr0 (lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith))))
  -- the punctured ball is inside the open rectangle
  have hball_rect : ∀ z : ℂ, z ∈ Metric.ball z₀ ρ → z ≠ z₀ →
      x₁ < z.re ∧ z.re < x₂ ∧ y₁ < z.im ∧ z.im < y₂ := by
    intro z hz hzne
    obtain ⟨hre, him⟩ := abs_re_sub_lt_of_mem_ball hz
    have hre' := abs_lt.mp hre
    have him' := abs_lt.mp him
    exact ⟨by linarith [hre'.1, hρre₁], by linarith [hre'.2, hρre₂],
      by linarith [him'.1, hρim₁], by linarith [him'.2, hρim₂]⟩
  set g : ℂ → ℂ := fun z => f z - c / (z - z₀) with hgdef
  -- `g` is holomorphic on the punctured ball
  have hgd : DifferentiableOn ℂ g (Metric.ball z₀ ρ \ {z₀}) := by
    intro z hz
    have hzne : z ≠ z₀ := hz.2
    have hb := hball_rect z hz.1 hzne
    have h1 : DifferentiableAt ℂ f z := hhol z hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hzne
    have h2 : DifferentiableAt ℂ (fun w : ℂ => c / (w - z₀)) z :=
      (differentiableAt_const c).div (differentiableAt_id.sub_const z₀) (sub_ne_zero.mpr hzne)
    have : DifferentiableAt ℂ g z := by
      rw [hgdef]
      exact h1.sub h2
    exact this.differentiableWithinAt
  -- `g` is bounded on the punctured ball
  have hbdd_ball : BddAbove (norm ∘ g '' (Metric.ball z₀ ρ \ {z₀})) := by
    refine ⟨M, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    have hzb : z ∈ Metric.ball z₀ ρ := hz.1
    rw [Metric.mem_ball, dist_eq_norm] at hzb
    exact hrM z hz.2 (lt_of_lt_of_le hzb hρr)
  -- Riemann: the update of `g` at `z₀` is holomorphic on the ball
  have hRiem := Complex.differentiableOn_update_limUnder_of_bddAbove
    (f := g) (s := Metric.ball z₀ ρ) (c := z₀) (Metric.ball_mem_nhds z₀ hρ0) hgd hbdd_ball
  -- the correct function for the residue theorem
  set G : ℂ → ℂ := fun z => Function.update g z₀ (limUnder (𝓝[≠] z₀) g) z + c / (z - z₀) with hGdef
  have hG_off : ∀ z : ℂ, z ≠ z₀ → G z = f z := by
    intro z hzne
    simp only [hGdef, hgdef, Function.update_of_ne hzne]
    ring
  -- the three hypotheses of `residue_rectangle`
  have hcontG : ContinuousOn G
      ({z : ℂ | x₁ ≤ z.re ∧ z.re ≤ x₂ ∧ y₁ ≤ z.im ∧ z.im ≤ y₂} \ {z₀}) :=
    hcont.congr fun z hz => hG_off z hz.2
  have hholG : ∀ z : ℂ, x₁ < z.re → z.re < x₂ → y₁ < z.im → z.im < y₂ → z ≠ z₀ →
      DifferentiableAt ℂ G z := by
    intro z h₁ h₂ h₃ h₄ hne
    have hzf : DifferentiableAt ℂ f z := hhol z h₁ h₂ h₃ h₄ hne
    have hzg : DifferentiableAt ℂ (Function.update g z₀ (limUnder (𝓝[≠] z₀) g)) z := by
      have : Function.update g z₀ (limUnder (𝓝[≠] z₀) g) =ᶠ[𝓝 z] g :=
        Filter.eventually_of_mem (isOpen_ne.mem_nhds hne)
          (fun w hw => Function.update_of_ne hw (limUnder (𝓝[≠] z₀) g) g)
      rw [this.differentiableAt_iff]
      rw [hgdef]
      exact hzf.sub ((differentiableAt_const c).div (differentiableAt_id.sub_const z₀)
        (sub_ne_zero.mpr hne))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => c / (w - z₀)) z :=
      (differentiableAt_const c).div (differentiableAt_id.sub_const z₀) (sub_ne_zero.mpr hne)
    have : DifferentiableAt ℂ G z := by
      rw [hGdef]
      exact hzg.add h2
    exact this
  have hremG : DifferentiableAt ℂ (fun z => G z - c / (z - z₀)) z₀ := by
    have hfun : (fun z => G z - c / (z - z₀))
        = Function.update g z₀ (limUnder (𝓝[≠] z₀) g) := by
      funext z
      rw [hGdef]
      ring
    rw [hfun]
    exact hRiem.differentiableAt (Metric.ball_mem_nhds z₀ hρ0)
  have hmain := residue_rectangle G z₀ c x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hcontG hholG hremG
  -- the edge integrals of `G` and `f` agree
  have edge_bot : (∫ x : ℝ in x₁..x₂, G ((x : ℂ) + (y₁ : ℂ) * Complex.I))
      = (∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    refine hG_off _ ?_
    intro h
    have : ((x : ℂ) + (y₁ : ℂ) * Complex.I).im = y₁ := by simp
    rw [h] at this
    linarith
  have edge_top : (∫ x : ℝ in x₁..x₂, G ((x : ℂ) + (y₂ : ℂ) * Complex.I))
      = (∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₂ : ℂ) * Complex.I)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    refine hG_off _ ?_
    intro h
    have : ((x : ℂ) + (y₂ : ℂ) * Complex.I).im = y₂ := by simp
    rw [h] at this
    linarith
  have edge_right : (∫ y : ℝ in y₁..y₂, G ((x₂ : ℂ) + (y : ℂ) * Complex.I))
      = (∫ y : ℝ in y₁..y₂, f ((x₂ : ℂ) + (y : ℂ) * Complex.I)) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    refine hG_off _ ?_
    intro h
    have : ((x₂ : ℂ) + (y : ℂ) * Complex.I).re = x₂ := by simp
    rw [h] at this
    linarith
  have edge_left : (∫ y : ℝ in y₁..y₂, G ((x₁ : ℂ) + (y : ℂ) * Complex.I))
      = (∫ y : ℝ in y₁..y₂, f ((x₁ : ℂ) + (y : ℂ) * Complex.I)) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    refine hG_off _ ?_
    intro h
    have : ((x₁ : ℂ) + (y : ℂ) * Complex.I).re = x₁ := by simp
    rw [h] at this
    linarith
  rw [edge_bot, edge_top, edge_right, edge_left] at hmain
  exact hmain

end Work.Asymptotics
