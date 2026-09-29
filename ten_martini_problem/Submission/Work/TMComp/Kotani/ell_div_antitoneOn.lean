import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.two_ell
import Submission.Work.TMComp.Kotani.inv_N_le
import Submission.Work.TMComp.Kotani.L6_algebra
import Submission.Work.TMComp.Kotani.hasDerivAt_ell
import Submission.Work.TMComp.Kotani.ell_defect_le

/-!
# Unconditional antitonicity of `ε ↦ ℓ(E₀ + i ε)/ε`

Let `ℓ(E) = ∫₀¹ log ‖m(E,x)‖ dx` (`ell`) and put `f(ε) = ℓ(E₀ + iε)/ε` for `ε > 0`.

The two analytic inputs are

* `hasDerivAt_ell`: `∂_ε ℓ(E₀ + iε) = ∫₀¹ im(-1/defect(E₀+iε, y)) dy`  (route step (L5)), and
* `ell_defect_le`: `∫₀¹ im(-1/defect(E, y)) dy ≤ ℓ(E)/Im E`  (the (K2) estimate, obtained from
  (L3) `∫ 1/N₁, ∫ 1/N₂ ≤ 2ℓ/ε` together with the algebraic identity (L6)).

Since `f = ℓ/ε` on `ε > 0` with
`f'(ε) = (∂_εℓ·ε − ℓ)/ε² = (∂_εℓ − ℓ/ε)/ε ≤ 0`,
`f` is antitone on `(0,∞)` (`antitoneOn_of_deriv_nonpos`).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

/-- **Unconditional antitonicity of `ℓ/ε`.** For every `α, lam` and every `E₀ : ℝ`, the
function `ε ↦ ∫₀¹ log ‖m(E₀+iε, x)‖ dx / ε` is antitone on `(0, ∞)`. -/
theorem ell_div_antitoneOn (α lam : ℝ) (E₀ : ℝ) :
    AntitoneOn
      (fun ε : ℝ => Work.TMComp.Kotani.ell α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) / ε)
      (Set.Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
  · -- continuity of `ε ↦ ℓ(E₀+iε)/ε` on `(0, ∞)`
    intro ε hε
    exact ((hasDerivAt_ell α lam E₀ ε hε).div (hasDerivAt_id ε)
      (ne_of_gt hε)).continuousAt.continuousWithinAt
  · -- differentiability of `ε ↦ ℓ(E₀+iε)/ε` on `(0, ∞)`
    rw [interior_Ioi]
    intro ε hε
    exact ((hasDerivAt_ell α lam E₀ ε hε).div (hasDerivAt_id ε)
      (ne_of_gt hε)).differentiableAt.differentiableWithinAt
  · -- the derivative is `≤ 0`
    rw [interior_Ioi]
    intro ε hε
    have hEim : ((E₀ : ℂ) + (ε : ℂ) * Complex.I).im = ε := by simp
    have hE : 0 < ((E₀ : ℂ) + (ε : ℂ) * Complex.I).im := by rw [hEim]; exact hε
    have hdiv : HasDerivAt
        (fun t : ℝ => Work.TMComp.Kotani.ell α lam ((E₀ : ℂ) + (t : ℂ) * Complex.I) / t)
        (((∫ y in (0 : ℝ)..1,
            (-1 / Work.TMComp.Kotani.defect α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y).im) * ε
          - Work.TMComp.Kotani.ell α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) * 1) / ε ^ 2) ε :=
      (hasDerivAt_ell α lam E₀ ε hε).div (hasDerivAt_id ε) (ne_of_gt hε)
    rw [hdiv.deriv]
    have hle := ell_defect_le α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) hE
    rw [hEim] at hle
    have hnum : (∫ y in (0 : ℝ)..1,
          (-1 / Work.TMComp.Kotani.defect α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y).im) * ε
        - Work.TMComp.Kotani.ell α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) * 1 ≤ 0 := by
      have h2 : (Work.TMComp.Kotani.ell α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) / ε) * ε
          = Work.TMComp.Kotani.ell α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hε)]
      have h1 := mul_le_mul_of_nonneg_right hle (le_of_lt hε)
      rw [h2] at h1
      linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg ε)

end Work.TMComp.Kotani
