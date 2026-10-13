import Mathlib
import Submission.Work.WilE5.Basic

namespace Work.WilE5.Cells

theorem khovAtomEval {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (ε : ℝ)
    (f : WilkiesDesign.E.EAPoly k r) (x : Fin k → ℝ) :
    WilkiesDesign.E.eaEval c ((f + MvPolynomial.C ε) ^ 2 * (f - MvPolynomial.C ε) ^ 2) x =
      (WilkiesDesign.E.eaEval c f x + ε) ^ 2 * (WilkiesDesign.E.eaEval c f x - ε) ^ 2 := by
  simp only [WilkiesDesign.E.eaEval, MvPolynomial.eval_add, MvPolynomial.eval_sub,
    MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_C]

end Work.WilE5.Cells
