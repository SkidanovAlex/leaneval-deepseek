/-
  WilE8 — clearing denominators along `psi`.

  For a polynomial `P` in `n` variables we want to express the condition
  `P (y_i / sqrt (1 - y_i^2))_i = 0` (which is what `psiV^{-1}` of the hyperplane
  `{P = 0}` gives, with `w_i = sqrt (1 - y_i^2)`) as a *polynomial* condition in `(y, w)`.
  Multiplying by `∏ i, w i ^ P.totalDegree` clears the denominators:
  `∏ᵢ wᵢ^d * P(yᵢ/wᵢ) = (clearDenom P) (y, w)`, where `d = P.totalDegree`.
-/
import Submission.Work.WilE8.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE8
open WilkiesDesign WilkiesDesign.E

/-- The polynomial `∑_{a ∈ support P} c_a ∏ᵢ yᵢ^{aᵢ} ∏ᵢ wᵢ^{deg P - aᵢ}`, i.e. `P(y/w)`
with denominators cleared.  Variables `Sum.inl i` are the `yᵢ`, `Sum.inr i` the `wᵢ`. -/
noncomputable def clearDenom {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n ⊕ Fin n) ℝ :=
  P.support.sum fun a =>
    MvPolynomial.C (P.coeff a) * (∏ i, MvPolynomial.X (Sum.inl i) ^ a i) *
      (∏ i, MvPolynomial.X (Sum.inr i) ^ (P.totalDegree - a i))

end Work.WilE8
