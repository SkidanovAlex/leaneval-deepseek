import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Each coordinate of the curve point `ptC ℓ z` is an entire function of `z`. -/
private lemma differentiable_ptC_apply {r : ℕ} (ℓ : Fin r → ℂ) (n : Fin (r + 1)) :
    Differentiable ℂ (fun z => ptC ℓ z n) := by
  refine Fin.cases ?_ ?_ n
  · show Differentiable ℂ (fun z : ℂ => z)
    exact differentiable_id
  · intro i
    show Differentiable ℂ (fun z : ℂ => Complex.exp (z * ℓ i))
    exact Complex.differentiable_exp.comp (differentiable_id.mul_const (ℓ i))

/-- The curve evaluation `z ↦ P(z, e^{zℓ₁}, …)` is entire (a finite sum of `z^k e^{zλ}`). -/
theorem differentiable_fAt {r : ℕ} (ℓ : Fin r → ℂ) (P : MvPolynomial (Fin (r + 1)) ℂ) :
    Differentiable ℂ (fAt ℓ P) := by
  change Differentiable ℂ (fun z => MvPolynomial.eval (ptC ℓ z) P)
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact differentiable_const a
  | add p q hp hq =>
    have h : (fun z => MvPolynomial.eval (ptC ℓ z) (p + q))
        = (fun z => MvPolynomial.eval (ptC ℓ z) p)
          + (fun z => MvPolynomial.eval (ptC ℓ z) q) := by
      funext z; simp [MvPolynomial.eval_add]
    rw [h]; exact hp.add hq
  | mul_X p n hp =>
    have h : (fun z => MvPolynomial.eval (ptC ℓ z) (p * MvPolynomial.X n))
        = (fun z => MvPolynomial.eval (ptC ℓ z) p)
          * (fun z => ptC ℓ z n) := by
      funext z; simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    rw [h]; exact hp.mul (differentiable_ptC_apply ℓ n)

end Work.BW
