/-
  WilE10 — the branch polynomial.

  When a rexp-polynomial is evaluated on a branch where each inner variable `tᵢ` is either
  "small" (`|tᵢ| ≤ 1`, so `rexp tᵢ = exp tᵢ`) or "large" (`|tᵢ| > 1`, so `rexp tᵢ = 0`), the
  equation `P(t, rexp t) = 0` can be replaced by a *polynomial* equation in the small variables
  `tᵢ`, the reciprocals `1/tᵢ` of the large ones, and the chain values `exp tᵢ`. This file defines
  that polynomial; the identity relating its evaluation to `P(t, rexp t)` is proved in
  `branchPoly_eval`.
-/
import Submission.Work.WilE10.Vocab

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE10

open WilkiesDesign WilkiesDesign.E

/-- The branch polynomial. For each monomial of `P` and each index `i`:
* in the "small" branch (`ε i = true`) the variable `Sum.inl i` becomes the coordinate `tv i` and
  the variable `Sum.inr i` becomes the chain variable `ev i` (which is evaluated at `exp` of the
  coordinate `tv i`);
* in the "large" branch (`ε i = false`) the variable `Sum.inl i`, raised to the exponent `a` of
  the monomial, is replaced by the reciprocal coordinate `sv i` raised to `D - a` (clearing the
  denominator, using `D ≥ a`), and the variable `Sum.inr i` is replaced by `0` (raised to the
  monomial exponent, so it contributes `1` when the exponent is `0` and `0` otherwise).

The evaluation identity is `branchPoly_eval`. -/
def branchPoly {ι : Type*} [Fintype ι] (D : ℕ) (ε : ι → Bool) {K r : ℕ} (tv sv : ι → Fin K)
    (ev : ι → Fin r) (P : MvPolynomial (ι ⊕ ι) ℝ) : MvPolynomial (Fin K ⊕ Fin r) ℝ :=
  P.support.sum fun m =>
    MvPolynomial.C (P.coeff m) * ∏ i,
      (if ε i then (MvPolynomial.X (Sum.inl (tv i))) ^ (m (Sum.inl i)) *
          (MvPolynomial.X (Sum.inr (ev i))) ^ (m (Sum.inr i))
        else (MvPolynomial.X (Sum.inl (sv i))) ^ (D - m (Sum.inl i)) *
          (0 : MvPolynomial (Fin K ⊕ Fin r) ℝ) ^ (m (Sum.inr i)))

end Work.WilE10
