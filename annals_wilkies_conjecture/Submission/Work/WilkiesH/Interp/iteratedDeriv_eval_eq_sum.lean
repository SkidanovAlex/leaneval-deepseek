import Mathlib

namespace Work.WilkiesH.Interp

theorem iteratedDeriv_eval_eq_sum {n j : ℕ} (P : MvPolynomial (Fin n) ℝ) (ψ : Fin n → ℝ → ℝ)
    (s₀ : ℝ) (hdiff : ∀ i, ContDiffAt ℝ (j : ℕ) (ψ i) s₀) :
    iteratedDeriv j (fun s => P.eval (fun i => ψ i s)) s₀
      = ∑ m ∈ P.support, P.coeff m * iteratedDeriv j (fun s => ∏ i, (ψ i s) ^ (m i)) s₀ := by
  -- Write `P.eval` of the tuple `fun i => ψ i s` as the explicit finite sum over `P.support`.
  have hfun : (fun s => P.eval (fun i => ψ i s)) =
      fun s => ∑ m ∈ P.support, P.coeff m * ∏ i, (ψ i s) ^ (m i) := by
    funext s
    rw [MvPolynomial.eval_eq']
  rw [hfun, iteratedDeriv_fun_sum]
  · -- Pull out the constant coefficient in front of each iterated derivative.
    simp only [iteratedDeriv_const_mul_field]
  · -- Each summand is `C^j` at `s₀`, so `iteratedDeriv_fun_sum` applies.
    intro m _
    refine ContDiffAt.mul ?_ ?_
    · exact contDiffAt_const
    · exact contDiffAt_prod (t := Finset.univ) (fun i _ => (hdiff i).pow (m i))

end Work.WilkiesH.Interp
