import Mathlib
import Submission.Work.Asymptotics.gaussian_bound

namespace Work.CKFinal

open Polynomial

/-- Every coefficient of `gaussPoly · l` is a differentiable function of the parameter. -/
theorem gaussPoly_coeff_differentiable (l k : ℕ) :
    Differentiable ℂ (fun z : ℂ => (Work.Asymptotics.gaussPoly z l).coeff k) := by
  induction l generalizing k with
  | zero =>
      have h0 : (fun z : ℂ => (Work.Asymptotics.gaussPoly z 0).coeff k)
          = fun _ => (1 : Polynomial ℂ).coeff k := by
        funext z; rw [Work.Asymptotics.gaussPoly_zero]
      rw [h0]
      exact differentiable_const _
  | succ m ih =>
      by_cases hk : k = 0
      · subst hk
        have h : (fun z : ℂ => (Work.Asymptotics.gaussPoly z (m + 1)).coeff 0)
            = fun z => (Work.Asymptotics.gaussPoly z m).coeff 1 := by
          funext z
          rw [Work.Asymptotics.gaussPoly_succ, Polynomial.coeff_sub,
              Polynomial.coeff_derivative, Polynomial.coeff_C_mul,
              Polynomial.coeff_X_mul_zero]
          ring
        rw [h]
        exact ih 1
      · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        have h : (fun z : ℂ => (Work.Asymptotics.gaussPoly z (m + 1)).coeff (k' + 1))
            = fun z => (Work.Asymptotics.gaussPoly z m).coeff (k' + 1 + 1) * ((k' : ℂ) + 1 + 1)
                - 2 * z * (Work.Asymptotics.gaussPoly z m).coeff k' := by
          funext z
          rw [Work.Asymptotics.gaussPoly_succ, Polynomial.coeff_sub,
              Polynomial.coeff_derivative, Polynomial.coeff_C_mul,
              Polynomial.coeff_X_mul]
          push_cast
          ring
        rw [h]
        apply Differentiable.sub
        · exact (ih (k' + 1 + 1)).mul_const _
        · apply Differentiable.mul
          · exact differentiable_id.const_mul 2
          · exact ih k'

/-- The evaluation `z ↦ (gaussPoly z l).eval y` is a polynomial function of `z`: it is a finite
sum of the coefficient functions `z ↦ (gaussPoly z l).coeff k`, which are differentiable. -/
theorem differentiable_gaussPoly_eval (l : ℕ) (y : ℂ) :
    Differentiable ℂ (fun z : ℂ => (Work.Asymptotics.gaussPoly z l).eval y) := by
  have hcongr : (fun z : ℂ => (Work.Asymptotics.gaussPoly z l).eval y)
      = fun z => ∑ k ∈ Finset.range (l + 1),
          (Work.Asymptotics.gaussPoly z l).coeff k * y ^ k := by
    funext z
    exact Polynomial.eval_eq_sum_range' (n := l + 1)
      (Nat.lt_succ_of_le (Work.Asymptotics.gaussPoly_deg_and_coeff z l).1) y
  rw [hcongr]
  have hsum : (fun z : ℂ => ∑ k ∈ Finset.range (l + 1),
        (Work.Asymptotics.gaussPoly z l).coeff k * y ^ k)
      = ∑ k ∈ Finset.range (l + 1),
          (fun z : ℂ => (Work.Asymptotics.gaussPoly z l).coeff k * y ^ k) := by
    funext z
    simp only [Finset.sum_apply]
  rw [hsum]
  apply Differentiable.sum
  intro k hk
  exact (Work.CKFinal.gaussPoly_coeff_differentiable l k).mul_const _

end Work.CKFinal
