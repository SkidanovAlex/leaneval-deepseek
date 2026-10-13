/-
# `Weil/Main` — `SmoothOpen (psiSeries α (RemSource α ψ))` from the Weyl route

Instantiation of the two assembly steps of `Weil/Assembly.lean` with the pieces proved in this
directory:

* `remSourceFacts` — `SmoothOpen`, `OrthCond` and `L²`-integrability of the source
  `RemSource α ψ = α²·phiA α·ψ`;
* `modeTermBound` — the pointwise majorant `C(1+1/z)(m+1)^{-7/2}` of the mode terms;
* `psiSeriesUniform` — continuity of the mode series on `Q0` and local uniform convergence of
  the partial sums;
* `tendstoIntegralPsiTrunc` / `tendstoIntegralCsrc` — the two limit steps of the truncated weak
  identity;
* `bmodeUniform` — the uniform bound/convergence of the coefficient series `Σ b_m e_m`.

The final `smoothOpenR` is the smoothness conjunct of `psiSeries_solves_rem`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Weil.Defs
import Submission.Work.FTS.PhiStar.Series.Weil.Assembly
import Submission.Work.FTS.PhiStar.Series.Weil.remSourceFacts
import Submission.Work.FTS.PhiStar.Series.Weil.modeTermBound
import Submission.Work.FTS.PhiStar.Series.Weil.bmodeUniform
import Submission.Work.FTS.PhiStar.Series.Weil.psiSeriesUniform
import Submission.Work.FTS.PhiStar.Series.Weil.tendstoIntegralPsiTrunc
import Submission.Work.FTS.PhiStar.Series.Weil.tendstoIntegralCsrc
import Submission.Work.FTS.PhiStar.Defs
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

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false

/-- **The weak formulation of the mode series.** -/
theorem weakIdentity (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0,
          R α ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = ∫ p in Work.FTS.EllipticEst.Q0,
          Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  obtain ⟨hF, horth, hL2⟩ := remSourceFacts α ψ hψ
  obtain ⟨C, hC, hb⟩ := modeTermBound α ψ hα hα5 hψ
  obtain ⟨hbound, hconv⟩ := bmodeUniform α ψ hα hα5 hψ
  obtain ⟨-, hbox⟩ := psiSeriesUniform α ψ hα (by linarith) hψ hC hb
  refine weakIdentity_of_limits α ψ hF horth hL2 hα (by linarith) ?_ ?_
  · intro φ hφ hφc hφs
    refine tendstoIntegralPsiTrunc ?_ hφ hφc hφs
    intro a b c d ha hab hc hcd hd
    obtain ⟨hb1, hb2⟩ := hbox a b c d ha hab hc hcd hd
    exact ⟨⟨C * (1 + 1 / a) * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))), hb1⟩, hb2⟩
  · intro φ hφ hφc hφs
    exact tendstoIntegralCsrc α ψ hα hα5 hψ hbound hconv hφ hφc hφs

/-- **The smoothness of the remainder series on the open quadrant** — conjunct 1 of
`psiSeries_solves_rem`. -/
theorem smoothOpenR (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ) := by
  obtain ⟨hF, -, -⟩ := remSourceFacts α ψ hψ
  obtain ⟨C, hC, hb⟩ := modeTermBound α ψ hα hα5 hψ
  obtain ⟨hcont, -⟩ := psiSeriesUniform α ψ hα (by linarith) hψ hC hb
  exact smoothOpenR_of_parts α ψ hcont hF hα (weakIdentity α ψ hα hα5 hψ)

end Work.FTS.PhiStar.Series.Weil
