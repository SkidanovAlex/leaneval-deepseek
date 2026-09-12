import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Algebra.MvPolynomial

theorem contDiff_eval
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const (c := a)
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
      have hxi : ContDiff ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin n) => y i) :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
      simpa using hp.mul hxi

end Commons.Algebra.MvPolynomial