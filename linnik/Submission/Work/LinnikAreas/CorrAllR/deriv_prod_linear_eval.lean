import Mathlib

namespace Work.LinnikAreas.CorrAllR

/-- Logarithmic derivative of a product of linear factors: for a field `K`, shifts `c l` and a
point `x` at which no factor vanishes, `(∏_l (X + C (c_l)))'(x) = (∏_l (x + c_l)) · ∑_l (x + c_l)⁻¹`.
This is the general-`n` version of the `Fin 3` case proved privately in
`Submission/Commons/NumberTheory/DirichletCharacter/charCorrelation6_primeSq.lean`. -/
theorem deriv_prod_linear_eval {K : Type*} [Field K] {n : ℕ} (c : Fin n → K) (x : K)
    (h : ∀ l : Fin n, x + c l ≠ 0) :
    (∏ l : Fin n, (Polynomial.X + Polynomial.C (c l))).derivative.eval x
      = (∏ l : Fin n, (x + c l)) * (∑ l : Fin n, (x + c l)⁻¹) := by
  have hder : (∏ l : Fin n, (Polynomial.X + Polynomial.C (c l)) : Polynomial K).derivative
      = ∑ l : Fin n, ∏ j ∈ Finset.univ.erase l, (Polynomial.X + Polynomial.C (c j)) := by
    rw [Polynomial.derivative_prod_finset]
    simp
  have key : ∀ l : Fin n, (∏ j ∈ Finset.univ.erase l, (x + c j))
      = (∏ j : Fin n, (x + c j)) * (x + c l)⁻¹ := by
    intro l
    have hmul := Finset.prod_erase_mul Finset.univ (fun j => (x + c j)) (Finset.mem_univ l)
    rw [← hmul, mul_assoc, mul_inv_cancel₀ (h l), mul_one]
  rw [hder, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  exact key l

end Work.LinnikAreas.CorrAllR
