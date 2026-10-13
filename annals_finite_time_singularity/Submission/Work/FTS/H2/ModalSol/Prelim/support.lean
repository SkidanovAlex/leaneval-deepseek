/-
# `ModalSol/Prelim/support` — the three support lemmas of the modal construction

STATEMENTS-ONLY MODULE (temporary `sorry`s): the proofs of the three lemmas below are being
proved in parallel in

* `Submission/Work/FTS/H2/ModalSol/Aux/radGreen_continuousOn.lean`,
* `Submission/Work/FTS/H2/ModalSol/Aux/integrableOn_mul_of_sq_integrable.lean`,
* `Submission/Work/FTS/H2/ModalSol/Prelim/rhs_limit_fts.lean`

(the `Aux/` module names are not portable on Lean 4.34, so this buildable copy carries the same
declarations).  Their proofs will be transported here verbatim once delivered; the `sorry`s are
temporary and are removed before the module is declared finished.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSol

/-- **Continuity of the mode-`m` radial Green's function** for a square-integrable source. -/
theorem radGreen_continuousOn (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0)) :
    ContinuousOn (Work.FTS.PhiStar.Radial.radGreen α m c) (Set.Ioi 0) := by
  sorry

/-- An `L²` function of the first variable times a continuous function on a compact box is
integrable on the box. -/
theorem integrableOn_mul_of_sq_integrable {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun z => c z ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    {a b c₀ d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c₀) (hcd : c₀ ≤ d)
    {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g (Set.Icc a b ×ˢ Set.Icc c₀ d)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => c p.1 * g p)
      (Set.Icc a b ×ˢ Set.Icc c₀ d) := by
  sorry

/-- **The source-side limit**: the truncated angular expansions of `F` converge weakly to `F`
against the test function `φ` with the weight `z ^ ((5-α)/α) cos θ`. -/
theorem rhs_limit_fts (α : ℝ) {F φ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Filter.Tendsto (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1 *
          Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop
      (nhds (∫ p in Work.FTS.EllipticEst.Q0,
        F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
  sorry

end Work.FTS.H2.ModalSol
