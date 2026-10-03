import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic

/-!
# Removing the trivial zero at the origin

If `g` is complex differentiable on a punctured ball around `0`, vanishes at `0` and has
derivative `1` there, then `g` factors as `ζ ↦ ζ * u ζ` with `u` analytic at `0` and `u 0 = 1`.

The factor is of course `u ζ = g ζ / ζ` for `ζ ≠ 0`, filled in with the value `1` at `0`. It is
analytic at `0` by Riemann's removable singularity theorem: it is differentiable on the punctured
ball and, by definition of the derivative, `(g ζ - g 0)/ζ → 1`, so it is continuous at `0` with
value `1`.
-/

namespace Work.Horn

theorem analyticAt_extension_of_hasDerivAt (g : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hdiff : DifferentiableOn ℂ g (Metric.ball 0 R \ {0})) (hg0 : g 0 = 0) (hder : HasDerivAt g 1 0) :
    ∃ u : ℂ → ℂ, u 0 = 1 ∧ AnalyticAt ℂ u 0 ∧ (∀ᶠ ζ in nhds (0 : ℂ), g ζ = ζ * u ζ) := by
  -- The candidate factor: `g ζ / ζ` away from `0`, and its limit `1` at `0`.
  set u : ℂ → ℂ := Function.update (fun ζ : ℂ => g ζ / ζ) 0 1 with hu
  have hu0 : u 0 = 1 := by rw [hu, Function.update_self]
  have hgdiv : ∀ ζ : ℂ, ζ ≠ 0 → u ζ = g ζ / ζ := by
    intro ζ hζ
    rw [hu, Function.update_of_ne hζ]
  -- Continuity at `0`: `g ζ / ζ` is the slope of `g` at `0`, whose limit is `g'(0) = 1`.
  have hcont : ContinuousAt u 0 := by
    rw [hu, continuousAt_update_same]
    have h := hasDerivAt_iff_tendsto_slope.mp hder
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z _
    rw [slope_def_field, sub_zero, hg0, sub_zero]
  -- Holomorphy on a punctured ball around `0`.
  have hdiff' : ∀ᶠ z in nhdsWithin (0 : ℂ) ({0}ᶜ), DifferentiableAt ℂ u z := by
    have hball : Metric.ball (0 : ℂ) R ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
    filter_upwards [self_mem_nhdsWithin, hball] with z hz hzball
    have heq : u =ᶠ[nhds z] (fun w : ℂ => g w / w) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      rw [hu, Function.update_of_ne hw]
    rw [heq.differentiableAt_iff]
    have hgz : DifferentiableAt ℂ g z :=
      hdiff.differentiableAt
        (Filter.inter_mem (Metric.isOpen_ball.mem_nhds hzball) (isOpen_ne.mem_nhds hz))
    exact hgz.div differentiableAt_id hz
  have hanal : AnalyticAt ℂ u 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff' hcont
  refine ⟨u, hu0, hanal, ?_⟩
  filter_upwards with ζ
  by_cases hζ : ζ = 0
  · subst hζ; simp [hg0, hu0]
  · rw [hgdiv ζ hζ, mul_div_cancel₀ (g ζ) hζ]

end Work.Horn
