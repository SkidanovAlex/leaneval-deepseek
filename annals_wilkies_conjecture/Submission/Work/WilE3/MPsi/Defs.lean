import Mathlib
import Submission.Work.WilE3.Taylor.MaximalPsi
import Submission.Work.WilE3.Taylor.hasLoj_of_multiplicity
import Submission.Work.WilE3.Realify.MultiplicityBound_of_ET
import Submission.Work.WilE3.eaEval_analytic

/-!
  Route for `Work.WilE3.Taylor.maximalPsiNode` ("ascent + projection", design
  `sources/wilkiesE3mpsi/wilkies_e3_maximalpsi.md`):

  * `psiProd B = ∏ g` over the strict inequalities, `resid B = ∑ f ^ 2` over the equations and
    `phiPen B ν = P · (P ^ (2ν) − S)` -- the penalised product whose positivity on
    `{g ≥ 0} ∩ {P ^ (2ν) ≥ S}` is equivalent to "all `g > 0` and `S < P ^ (2ν)`";
  * the two analytic inputs are the PROVED `Work.WilE3.Taylor.ea_grad_of_multiplicity` (effective
    gradient inequality for the single EA polynomial `phiPen B ν`) and the PROVED
    `Work.WilE3.Taylor.hasLoj_of_multiplicity` (residual Łojasiewicz inequality for `B.eqs`).
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

namespace Work.WilE3.MPsi

variable {k r : ℕ}

/-- `P = ∏ g` over the strict inequalities of `B` (the product, `1` when `B.pos` is empty). -/
def psiProd (B : Basic k r) : EAPoly k r := B.pos.prod

/-- `S = ∑ f ^ 2` over the equations of `B` (the sum of squares, `0` when `B.eqs` is empty). -/
def resid (B : Basic k r) : EAPoly k r := (B.eqs.map (· ^ 2)).sum

/-- The penalised product `Φ_ν = P · (P ^ (2ν) − S)`.  On `{g ≥ 0} ∩ {P ^ (2ν) ≥ S}` one has
`Φ_ν > 0` exactly when all the `g` are positive and `S < P ^ (2ν)`. -/
def phiPen (B : Basic k r) (ν : ℕ) : EAPoly k r :=
  psiProd B * (psiProd B ^ (2 * ν) - resid B)

/-- `Polynomial.eval` on `ℕ` is monotone. -/
theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  have hpow : ∀ i : ℕ, a ^ i ≤ b ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, pow_succ]; exact Nat.mul_le_mul ih h
  rw [Polynomial.eval_eq_sum_range a, Polynomial.eval_eq_sum_range b]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul le_rfl (hpow i)

end Work.WilE3.MPsi
