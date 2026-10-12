import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LGW.PeriodiseLe
import Submission.Work.BoseFixR.LGW.STDerivBound
import Submission.Work.BoseFixR.LocaliseGradWideAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LocaliseGradWideFixed` — the wide localisation inequality, correctly parenthesised

This is the *intended* statement of `Work.BoseFixR.LocaliseGradWideNow` /
`Work.BoseFixR.LocaliseGradWide`, with the right-hand side parenthesised so that the second
term is `ℓ⁻² · ∫_{boxL ℓ} φ²` and **not** the constant `∫_{boxL ℓ} φ²` multiplied by `ℓ⁻²`
and then integrated (which is what the unparenthesised text

  `4000 * (∫ x in boxL ℓ, ‖gradient φ x‖ ^ 2 + (ℓ ^ 2)⁻¹ * ∫ x in boxL ℓ, (φ x) ^ 2)`

means: the body of the *outer* integral `∫ x in boxL ℓ, ⋯` extends over the whole parenthesised
expression, so the inner `∫ x in boxL ℓ, (φ x)^2` is a *constant* as far as `x` is concerned and
contributes `ℓ⁻² · ℓ³ · ∫ φ² = ℓ · ∫ φ²`, not `ℓ⁻² ∫ φ²`).

With the offending `∫ x in boxL ℓ, ‖gradient φ x‖ ^ 2` **not** parenthesised, the resulting
inequality is false: taking `ℓ = R = 1/10` and `φ ≡ 1` (which is `ℓ`-periodic and `C²`), the
right-hand side is `4000 · ∫_{boxL ℓ} ℓ⁻² · |boxL ℓ| = 4000 ℓ⁴ = 0.4`, while
`∫ ‖∇(η·1)‖² = ∫ ‖∇η‖² ≥ 4πℓ = 1.2566…` for *every* admissible `η`, by the Newtonian capacity of
the ball: `cap (B_r) = 4πr`.

The statement below is proved by `Work.BoseFixR.localise_ineq` from the two delegated lemmas
`Work.BoseFixR.LGW.STDerivBound` (`|deriv Real.smoothTransition| ≤ 45/16`) and
`Work.BoseFixR.LGW.PeriodiseLe` (the lattice-periodisation bound with multiplicity `125`).
-/

noncomputable section

open scoped Real Topology BigOperators Pointwise
open MeasureTheory

namespace Work.BoseFixR

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The wide localisation inequality (correct parenthesisation).**  For `0 < ℓ`, `0 ≤ R ≤ ℓ`
there is a `C²` cutoff `η` which is `1` on the closed ball of radius `R`, takes values in `[0,1]`
and is compactly supported, such that for every `ℓ`-periodic `φ`

  `∫_{ℝ³} ‖∇(η φ)‖² ≤ 4000 * (∫_{boxL ℓ} ‖∇φ‖² + ℓ⁻² ∫_{boxL ℓ} φ²)`. -/
theorem LocaliseGradWideFixed {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hRℓ : R ≤ ℓ) :
    ∃ η : E3 → ℝ,
      (∀ x, ‖x‖ ≤ R → η x = 1) ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      ContDiff ℝ 2 η ∧ HasCompactSupport η ∧
      ∀ φ : E3 → ℝ,
        (∀ (n : Fin 3 → ℤ) (x : E3), φ (x + lat ℓ n) = φ x) →
        ContDiff ℝ 2 φ →
        ∫ x, ‖gradient (fun y => η y * φ y) x‖ ^ 2
          ≤ 4000 * ((∫ x in boxL ℓ, ‖gradient φ x‖ ^ 2)
              + (ℓ ^ 2)⁻¹ * (∫ x in boxL ℓ, (φ x) ^ 2)) := by
  refine ⟨etaOf ℓ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact etaOf_eq_one hℓ (le_trans hx hRℓ)
  · intro x; exact etaOf_mem ℓ x
  · exact contDiff_etaOf ℓ
  · exact hasCompactSupport_etaOf hℓ
  · intro φ hper hφ
    exact localise_ineq hℓ LGW.STDerivBound (LGW.PeriodiseLe (ℓ := ℓ) hℓ) φ hper hφ

end Work.BoseFixR
