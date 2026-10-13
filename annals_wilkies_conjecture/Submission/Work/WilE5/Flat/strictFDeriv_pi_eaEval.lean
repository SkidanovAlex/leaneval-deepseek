import Mathlib
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.Strat.hasStrictFDerivAt_eaEval

namespace Work.WilE5.Flat

open WilkiesDesign WilkiesDesign.E

/-- The vector-valued map `z ↦ (a ↦ eaEval c (h a) z)` is strictly differentiable (the derivative
is left as `fderiv`; its explicit form is `fderiv_pi_eaEval_apply`).  Route: `fderiv_pi` to
compute the derivative, `Work.WilE5.Flat.strictFDeriv_eaEval` (or `hasFDerivAt_eaEval`) for the
components, and `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt` (or `hasStrictFDerivAt_pi`,
Mathlib `Analysis/Calculus/FDeriv/Pi`) to assemble. -/
theorem strictFDeriv_pi_eaEval {k r j : ℕ} (c : EAChain k r)
    (h : Fin j → EAPoly k r) (x : Fin k → ℝ) :
    HasStrictFDerivAt (fun z : Fin k → ℝ => fun a : Fin j => eaEval c (h a) z)
      (fderiv ℝ (fun z : Fin k → ℝ => fun a : Fin j => eaEval c (h a) z) x) x := by
  have hst := hasStrictFDerivAt_pi.2 (fun a => Work.Strat.hasStrictFDerivAt_eaEval c (h a) x)
  rw [hst.hasFDerivAt.fderiv]
  exact hst

end Work.WilE5.Flat
