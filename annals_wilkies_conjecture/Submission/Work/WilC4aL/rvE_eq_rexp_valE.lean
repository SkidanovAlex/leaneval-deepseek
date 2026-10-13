import Mathlib
import Submission.Work.WilC4aL.Basic

namespace Work.WilC4aL

open WilkiesDesign
open scoped BigOperators

/-- On the piece described by `σ`, the two substitutions agree after applying `rexp`:
`rvE` is `rexp` of the true value `valE`.  For constant (parameter) variables this is
immediate; for a case variable `j` with `σ j = big` the value is `z j⁻¹` with `|z j| < 1`
and `z j ≠ 0`, so its `rexp` vanishes (as `rvE` does); for `small`/`one` coordinates
`|z j| < 1` resp. `z j ^ 2 = 1` put `z j` in the `exp` regime of `rexp`. -/
theorem rvE_eq_rexp_valE {k m : ℕ} (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC)
    (z : Fin (m + 2) → ℝ)
    (hbig : ∀ j : Fin (m + 2), σ j = VC.big → z j ≠ 0 ∧ |z j| < 1)
    (hsmall : ∀ j : Fin (m + 2), σ j = VC.small → |z j| < 1)
    (hone : ∀ j : Fin (m + 2), σ j = VC.one → z j ^ 2 = 1) :
    ∀ i : Fin (k + 2 + m), rvE cc σ i z = WilkiesDesign.rexp (valE cc σ i z) := by
  intro i
  rcases hp : piIdx i with j | j
  · -- constant (parameter) variable
    simp only [rvE, valE, hp, Sum.elim_inl]
  · rcases hc : σ j with _ | _ | _
    · -- `σ j = VC.small`
      simp only [rvE, valE, hp, Sum.elim_inr, hc, reduceCtorEq, ite_false]
      exact (rexp_of_abs_lt_one (hsmall j hc)).symm
    · -- `σ j = VC.one`
      simp only [rvE, valE, hp, Sum.elim_inr, hc, reduceCtorEq, ite_false]
      exact (rexp_of_sq_eq_one (hone j hc)).symm
    · -- `σ j = VC.big`
      simp only [rvE, valE, hp, Sum.elim_inr, hc, ite_true]
      exact (rexp_inv_of_abs_lt_one (hbig j hc).2 (hbig j hc).1).symm

end Work.WilC4aL
