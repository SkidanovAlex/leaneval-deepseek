import Mathlib

namespace Work.LinnikAreas.CorrAllR

/-- At a **simple** root of a product of linear factors the derivative does not vanish: if
`c i` occurs only once among the shifts `c l`, then `(∏_l (X + C (c_l)))'(-(c i)) ≠ 0`.  This is
the general-`n` version of the `Fin 3` case proved privately in
`Submission/Commons/NumberTheory/DirichletCharacter/charCorrelation6_primeSq.lean`. -/
theorem deriv_prod_linear_eval_simple_root {K : Type*} [Field K] {n : ℕ} (c : Fin n → K)
    (i : Fin n) (h : ∀ l : Fin n, l ≠ i → c l ≠ c i) :
    (∏ l : Fin n, (Polynomial.X + Polynomial.C (c l))).derivative.eval (-(c i)) ≠ 0 := by
  -- Split off the factor `X + C (c i)` and let `A` be the product of the remaining factors.
  -- Then `p = A * (X + C (c i))` and `p' = A' * (X + C (c i)) + A`, so at `x = -(c i)` the
  -- first summand dies and we are left with `A (-(c i)) = ∏_{l ≠ i} (c l - c i) ≠ 0`.
  set A : Polynomial K := ∏ l ∈ Finset.univ.erase i, (Polynomial.X + Polynomial.C (c l)) with hA
  have hfact : (∏ l : Fin n, (Polynomial.X + Polynomial.C (c l)))
      = A * (Polynomial.X + Polynomial.C (c i)) := by
    rw [hA]
    rw [Finset.prod_erase_mul (Finset.univ) (fun l => Polynomial.X + Polynomial.C (c l))
      (Finset.mem_univ i)]
  rw [hfact]
  have hderiv : Polynomial.derivative (A * (Polynomial.X + Polynomial.C (c i)))
      = Polynomial.derivative A * (Polynomial.X + Polynomial.C (c i)) + A := by
    rw [Polynomial.derivative_mul]
    simp
  rw [hderiv]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  rw [neg_add_cancel, mul_zero, zero_add]
  rw [hA]
  rw [Polynomial.eval_prod]
  rw [Finset.prod_ne_zero_iff]
  intro l hl
  rw [Finset.mem_erase] at hl
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  intro hc
  refine h l hl.1 ?_
  have h2 : c l - c i = 0 := by
    rw [sub_eq_add_neg, add_comm]
    exact hc
  exact sub_eq_zero.mp h2

end Work.LinnikAreas.CorrAllR
