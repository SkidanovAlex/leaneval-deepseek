import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
import Submission.Work.BSKinetic.winModeForm_sq_eq_dirichlet_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.bsOneBody_eq_dirichlet`

The one-body big-box kinetic form at the symbol `F(r) = r²` is the *full-space Dirichlet word*
of the windowed mean-free state:

`bsOneBody ℓ (·)² u ψ = ∫_x Σ_k (∂_k (χ_u · Q_{Λ(u)}ψ))²`.

Both sides only see the function `v := bsWin ℓ u · bsQ ℓ u ψ`, which is smooth and compactly
supported (the window `bsWin ℓ u` is `chiScale ℓ` translated by `ℓu`); the identity is then the
windowed Plancherel identity `Work.BSKinetic.winModeForm_sq_eq_dirichlet_mul` — the `p`-space
form `(2π)⁻³∫_p ‖p‖²‖kinFT v‖²` of `Σ_k∫(∂_k v)²`.

Note that no compact support of `ψ` itself is needed: the mean-free part `bsQ ℓ u ψ` is *not*
compactly supported, but the window kills it outside the moving box.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

theorem bsOneBody_eq_dirichlet {ℓ : ℝ} (hℓ : 0 < ℓ)
    (u : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    Work.BSKinetic.bsOneBody ℓ (fun r => r ^ 2) u ψ
      = ∫ x : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
          (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
              Work.BSKinetic.bsWin ℓ u y * Work.BSKinetic.bsQ ℓ u ψ y) x
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  -- The window `bsWin ℓ u` is smooth (it is `chiScale ℓ` composed with a translation) ...
  have hχ : ContDiff ℝ (⊤ : ENat) (bsWin ℓ u) := by
    have h : ContDiff ℝ (⊤ : ENat) (fun x : ℝ³ => x - ℓ • u) := by fun_prop
    exact (chiScale_contDiff (ne_of_gt hℓ)).comp h
  -- ... and the mean-free part of a smooth state is smooth (subtract the box mean) ...
  have hQ : ContDiff ℝ (⊤ : ENat) (bsQ ℓ u ψ) := by
    unfold bsQ
    exact hψ.sub contDiff_const
  -- ... so the windowed mean-free state is smooth and compactly supported.
  have hcs : HasCompactSupport (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) := by
    have h' : HasCompactSupport (chiScale ℓ) := chiScale_hasCompactSupport (ne_of_gt hℓ)
    exact (h'.comp_homeomorph (Homeomorph.subRight (ℓ • u))).mul_right
  -- The windowed Plancherel identity for the product `χ·u`.
  have key := winModeForm_sq_eq_dirichlet_mul (bsWin ℓ u) (bsQ ℓ u ψ) hχ hQ hcs
  -- `bsOneBody` is *definitionally* the windowed mode form at the window `bsWin ℓ u`.
  rw [show bsOneBody ℓ (fun r => r ^ 2) u ψ
      = Submission.BoseGases.winModeForm (bsWin ℓ u) (fun r => r ^ 2) (bsQ ℓ u ψ) from rfl]
  exact key

end Work.BSKinetic
