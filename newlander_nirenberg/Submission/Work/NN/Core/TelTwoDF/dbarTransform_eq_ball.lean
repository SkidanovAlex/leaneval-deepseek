import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.openSolDefs

namespace Work.NN.Core.TelTwoDF

open MeasureTheory Set

/-- Translation invariance of the Lebesgue integral on `ℂ`, in the form needed below: integrating
`F ∘ (c + ·)` over the disc `ball 0 ρ` is the same as integrating `F` over the shifted disc
`ball c ρ`.  This is the change of variables `ζ = c + w` (a measure-preserving bijection of `ℂ`),
restricted to the disc. -/
lemma setIntegral_ball_add (ρ : ℝ) (c : ℂ) (F : ℂ → ℂ) :
    ∫ w in Metric.ball (0 : ℂ) ρ, F (c + w) = ∫ ζ in Metric.ball c ρ, F ζ := by
  have hemp : MeasurableEmbedding (fun w : ℂ => c + w) := measurableEmbedding_addLeft c
  have hmap : Measure.map (fun w : ℂ => c + w) (volume : Measure ℂ) = volume :=
    map_add_left_eq_self volume c
  have hpre : (fun w : ℂ => c + w) ⁻¹' Metric.ball c ρ = Metric.ball 0 ρ := by
    ext w
    simp [Metric.mem_ball, dist_eq_norm]
  have h := hemp.setIntegral_map (μ := volume) F (Metric.ball c ρ)
  rw [hmap, hpre] at h
  exact h.symm

/-- **The Cauchy-type transform as an integral over the shifted disc.**

`Work.CR.Flat.Cauchy.dbarTransform ρ s g z = -(1/π) ∫_{‖w‖<ρ} g (z + w e_s) / w`.  Substituting
`ζ = z s + w` (translation invariance of Lebesgue measure) rewrites this as an integral over the
disc of radius `ρ` centred at `z s`:

`dbarTransform ρ s g z = -(1/π) ∫_{ζ ∈ ball (z s) ρ} g (update z s ζ) / (ζ - z s)`.

This "pole form" is the one needed to analyse the pole at `ζ = z s`: there the weight multiplying
`1/(ζ - z s)` can be a fixed compactly supported measure. -/
theorem dbarTransform_eq_ball {n : ℕ} {ρ : ℝ} (s : Fin n) {g : (Fin n → ℂ) → ℂ} (hg : Continuous g)
    (z : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.dbarTransform ρ s g z
      = -((Real.pi : ℂ))⁻¹ *
        ∫ ζ in Metric.ball (z s) ρ, g (Function.update z s ζ) / (ζ - z s) := by
  rw [Work.CR.Flat.Cauchy.dbarTransform]
  congr 1
  -- Both sides are the integral of the same function, the left one over `ball 0 ρ` after the
  -- substitution `ζ = z s + w`.
  have hupdate : ∀ w : ℂ,
      z + Function.update (0 : Fin n → ℂ) s w = Function.update z s (z s + w) := by
    intro w
    funext l
    by_cases hl : l = s
    · subst hl; simp
    · simp [hl]
  have hF : ∀ w : ℂ, g (Function.update z s (z s + w)) / w
      = (fun ζ => g (Function.update z s ζ) / (ζ - z s)) (z s + w) := by
    intro w
    show g (Function.update z s (z s + w)) / w
        = g (Function.update z s (z s + w)) / ((z s + w) - z s)
    rw [add_sub_cancel_left]
  simp_rw [hupdate, hF]
  exact setIntegral_ball_add ρ (z s) (fun ζ => g (Function.update z s ζ) / (ζ - z s))

end Work.NN.Core.TelTwoDF
