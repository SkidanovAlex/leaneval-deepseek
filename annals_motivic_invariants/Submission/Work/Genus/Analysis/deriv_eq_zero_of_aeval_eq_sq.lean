import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Analysis.ord_deriv_div_nonneg
import Submission.Work.Genus.Analysis.two_le_ordInf_deriv_div
import Submission.Work.Genus.Order.exists_algebraMap_eq_of_ord_nonneg
import Submission.Work.Genus.OrderInf.ordInf_polynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Analysis

/-- **The genus-zero input: `x` is constant along a solution of `A(x) = w²`.**  If `A` is a
squarefree cubic of degree `3`, `w ≠ 0` and `A(x) = w ^ 2` in `F(t)` (with `(2 : F) ≠ 0`), then
`deriv x = 0`.  Riemann–Hurwitz: a non-constant `x` would give a dominant morphism
`ℙ¹ → {v² = A(u)}` whose pullback of the invariant differential `ω = du / v` would be a rational
differential on `ℙ¹` with divisor of degree `2g(ℙ¹) - 2 = -2` and all orders `≥ 0`.

Route: suppose `deriv x ≠ 0` and put `g = deriv x / w`.  By
`Work.Genus.Analysis.ord_deriv_div_nonneg` every finite place has order `≥ 0`, so
`Work.Genus.Order.exists_algebraMap_eq_of_ord_nonneg` writes `g = algebraMap p` for a polynomial
`p`; then `Work.Genus.Analysis.two_le_ordInf_deriv_div` gives `2 ≤ ordInf g`, i.e.
`2 ≤ -p.natDegree` (`Work.Genus.OrderInf.ordInf_polynomial`) — impossible. -/
theorem deriv_eq_zero_of_aeval_eq_sq {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {A : Polynomial F}
    (hA : A.natDegree = 3) (hsq : IsCoprime A (Polynomial.derivative A)) {x w : RatFunc F}
    (hw : w ≠ 0) (heq : Polynomial.aeval x A = w ^ 2) : Work.Genus.deriv x = 0 := by
  by_contra hx'
  -- Every finite place is a non-pole of the invariant differential `deriv x / w`.
  have hnonneg : ∀ π : Polynomial F, Irreducible π →
      0 ≤ Work.Genus.ord π (Work.Genus.deriv x / w) :=
    fun π hπ => ord_deriv_div_nonneg h2 hA hsq hw hx' heq π hπ
  -- Hence it is a polynomial (regular away from infinity).
  obtain ⟨p, hp⟩ := Work.Genus.Order.exists_algebraMap_eq_of_ord_nonneg hnonneg
  -- At infinity it has a zero of order at least `2`.
  have h2le : 2 ≤ Work.Genus.ordInf (Work.Genus.deriv x / w) :=
    two_le_ordInf_deriv_div h2 hA hsq hw hx' heq
  -- So the polynomial has degree at most `-2`: impossible.
  rw [hp, Work.Genus.OrderInf.ordInf_polynomial] at h2le
  omega

end Work.Genus.Analysis
