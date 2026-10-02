import Mathlib
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Beltrami.cauchyTransform_decay

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory

/-- Decay at infinity of the Cauchy transform of a `C¹` compactly supported function, and of its
real Fréchet derivative.

The Beltrami file `Work.MRMT.Beltrami.cauchyTransform_decay` proves this with the hypothesis
`ContDiff ℝ ⊤ ψ`; its auxiliary lemmas, however, only ever use *continuity* of `ψ` together with
`HasCompactSupport ψ`.  Here we extract them directly, so the result holds for `ContDiff ℝ 1 ψ`. -/
theorem cauchyTransform_decay_of_contDiff_one {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖Work.MRMT.cauchyTransform ψ z‖ ≤ C / ‖z‖ ∧
      ‖fderiv ℝ (Work.MRMT.cauchyTransform ψ) z‖ ≤ C / ‖z‖ ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := Work.MRMT.Beltrami.decay_exists_support_radius ψ hs
  have hψc : Continuous ψ := hψ.continuous
  have hψint : Integrable (fun ζ => ‖ψ ζ‖) volume :=
    (hψc.integrable_of_hasCompactSupport hs).norm
  have hInn : 0 ≤ ∫ ζ, ‖ψ ζ‖ := integral_nonneg fun ζ => norm_nonneg _
  refine ⟨max (2 * (∫ ζ, ‖ψ ζ‖) / Real.pi) (16 * (∫ ζ, ‖ψ ζ‖)), max 1 (2 * M),
    le_trans (div_nonneg (mul_nonneg (by norm_num) hInn) Real.pi_pos.le) (le_max_left _ _), ?_⟩
  intro z hz
  have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hz
  have hz2 : 2 * M ≤ ‖z‖ := le_trans (le_max_right _ _) hz
  constructor
  · calc ‖Work.MRMT.cauchyTransform ψ z‖ ≤ (2 * (∫ ζ, ‖ψ ζ‖)) / Real.pi / ‖z‖ :=
        Work.MRMT.Beltrami.decay_cauchyTransform_le ψ hψint hM hz1 hz2
      _ ≤ max (2 * (∫ ζ, ‖ψ ζ‖) / Real.pi) (16 * (∫ ζ, ‖ψ ζ‖)) / ‖z‖ :=
        div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · calc ‖fderiv ℝ (Work.MRMT.cauchyTransform ψ) z‖ ≤ (16 * (∫ ζ, ‖ψ ζ‖)) / ‖z‖ ^ 2 :=
        Work.MRMT.Beltrami.decay_fderiv_le ψ hψc hψint hM hz1 hz2
      _ ≤ max (2 * (∫ ζ, ‖ψ ζ‖) / Real.pi) (16 * (∫ ζ, ‖ψ ζ‖)) / ‖z‖ ^ 2 :=
        div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)

end Work.MRMT.Found
