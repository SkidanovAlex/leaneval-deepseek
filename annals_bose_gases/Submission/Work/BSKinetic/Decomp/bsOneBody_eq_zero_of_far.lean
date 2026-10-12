import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.bsMean_eq_zero_of_far
import Submission.Work.BSKinetic.Decomp.exists_radius_eq_zero_of_hasCompactSupport
import Submission.Work.BSKinetic.Decomp.norm_ge_of_bsWin_ne_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.Decomp.bsOneBody_eq_zero_of_far`

The one-body big-box kinetic form

    `bsOneBody ℓ F u ψ = (2π)⁻³ ∫_p F(‖p‖)·‖kinFT (χ_u · Q_{Λ(u)}ψ)‖²`

is *localised*: for `ψ` smooth and compactly supported it vanishes as soon as the moving box
`Λ(u) = ℓu + acube ℓ` is far enough from the support of `ψ`, uniformly in the symbol `F`
(here `F = fsKinCoeff c = [· − c]₊²`).

Concretely, let `ψ` vanish outside the ball of radius `Rψ`
(`exists_radius_eq_zero_of_hasCompactSupport`) and let `Rψ + ℓ ≤ ℓ‖u‖`.  Then

* the window `bsWin ℓ u z = χ((z − ℓu)/ℓ)` vanishes whenever `‖z − ℓu‖ > ℓ/2`; if it does not
  vanish, then `‖z‖ ≥ ℓ‖u‖ − ℓ/2 ≥ Rψ` (`norm_ge_of_bsWin_ne_zero`), so `ψ z = 0`;
* the box mean `bsMean ℓ u ψ` vanishes as well, the whole moving box being outside the support
  of `ψ` (`bsMean_eq_zero_of_far`).

Hence the windowed mean-free state `χ_u · Q_{Λ(u)}ψ` is identically zero, its `p`-transform
vanishes, and so does the whole form.  The radius is `R = (Rψ + ℓ)/ℓ > 0`.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real

namespace Work.BSKinetic.Decomp

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- **The far-field vanishing of the one-body big-box kinetic form.**  For `ℓ > 0`, any
coefficient `c` and any smooth compactly supported `ψ`, there is `R ≥ 0` such that
`bsOneBody ℓ (fsKinCoeff c) u ψ = 0` for every `u` with `R ≤ ‖u‖` (the moving box `Λ(u) = ℓu +
acube ℓ` has then left the support of `ψ`). -/
theorem bsOneBody_eq_zero_of_far {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℝ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ u : EuclideanSpace ℝ (Fin 3), R ≤ ‖u‖ →
      Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u ψ = 0 := by
  obtain ⟨Rψ, hRψ0, hψzero⟩ := exists_radius_eq_zero_of_hasCompactSupport hcs
  refine ⟨(Rψ + ℓ) / ℓ, div_nonneg (by linarith) hℓ.le, ?_⟩
  intro u hu
  -- the moving box is far from the support of `ψ`
  have hℓR : ℓ * ((Rψ + ℓ) / ℓ) = Rψ + ℓ := by field_simp
  have hℓu : Rψ + ℓ ≤ ℓ * ‖u‖ := by
    have h1 : ℓ * ((Rψ + ℓ) / ℓ) ≤ ℓ * ‖u‖ := mul_le_mul_of_nonneg_left hu hℓ.le
    linarith
  -- the window times the mean-free part is identically zero
  have hprod : (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) *
      (Work.BSKinetic.bsQ ℓ u ψ z : ℂ)) = fun _ => 0 := by
    funext z
    by_cases hz : Work.BSKinetic.bsWin ℓ u z = 0
    · rw [hz]; simp
    · have hzfar : Rψ ≤ ‖z‖ := norm_ge_of_bsWin_ne_zero hℓ hℓu hz
      have hψz : ψ z = 0 := hψzero z hzfar
      have hmean : Work.BSKinetic.bsMean ℓ u ψ = 0 := bsMean_eq_zero_of_far hℓ hψzero hℓu
      simp [Work.BSKinetic.bsQ, hψz, hmean]
  rw [Work.BSKinetic.bsOneBody, hprod]
  simp [Submission.BoseGases.kinFT]

end Work.BSKinetic.Decomp
