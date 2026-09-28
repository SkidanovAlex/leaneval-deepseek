import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.HP2

open MvPolynomial Finset

/-- `Mon.toFinsupp` is injective: it is `Finsupp.equivFunOnFinite.symm` applied to the (injective)
coercion of the exponent vector to `ℕ`. -/
private lemma mon_toFinsupp_injective {d n : ℕ} :
    Function.Injective (Mon.toFinsupp (d := d) (n := n)) := by
  intro m₁ m₂ h
  apply Subtype.ext
  funext i
  have hfun : (fun i => (m₁.1 i : ℕ)) = (fun i => (m₂.1 i : ℕ)) := by
    have := congrArg (⇑(Finsupp.equivFunOnFinite (α := Fin (n + 1)) (M := ℕ))) h
    simpa [Mon.toFinsupp, Equiv.apply_symm_apply] using this
  exact Fin.ext (congrFun hfun i)

/-- A form of degree `d` in `n+1` variables with real coefficients `b` which is not the zero
coefficient vector is not the zero function on `ℝ^{n+1}`.

Route.  Write `p := ∑ μ, MvPolynomial.monomial (Mon.toFinsupp μ) (b μ) : MvPolynomial (Fin (n+1)) ℝ`
and check `p.eval x = formEvalR d n b x`.  `p ≠ 0`: the coefficient of `Mon.toFinsupp μ₀` is `b μ₀`
for the `μ₀` with `b μ₀ ≠ 0` (`MvPolynomial.coeff_sum`, `MvPolynomial.coeff_monomial`,
`Finset.sum_eq_single`, together with injectivity of `Mon.toFinsupp`).  Then apply
`MvPolynomial.funext` (contrapositive) to get `x` with `p.eval x ≠ 0`. -/
theorem formEval_ne_zero {d n : ℕ} (b : Mon d n → ℝ) (hb : b ≠ 0) :
    ∃ x : Fin (n + 1) → ℝ, formEvalR d n b x ≠ 0 := by
  -- the polynomial carrying the coefficients `b`
  set p : MvPolynomial (Fin (n + 1)) ℝ :=
    ∑ μ, MvPolynomial.monomial (Mon.toFinsupp μ) (b μ) with hp
  -- `p` is nonzero, since the coefficient of the exponent vector supporting `b` is `b μ₀`
  have hpne : p ≠ 0 := by
    obtain ⟨μ₀, hμ₀⟩ := Function.ne_iff.mp hb
    intro hzero
    have hcoeff : p.coeff (Mon.toFinsupp μ₀) = b μ₀ := by
      rw [hp, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single μ₀]
      · rw [MvPolynomial.coeff_monomial, ite_eq_left rfl]
      · intro μ _ hne
        rw [MvPolynomial.coeff_monomial, ite_eq_right (fun hc => hne (mon_toFinsupp_injective hc))]
      · intro h
        exact absurd (Finset.mem_univ μ₀) h
    rw [hzero] at hcoeff
    simp at hcoeff
    exact hμ₀ hcoeff.symm
  -- `p` evaluates to `formEvalR d n b`
  have heval : ∀ x : Fin (n + 1) → ℝ, MvPolynomial.eval x p = formEvalR d n b x := by
    intro x
    rw [hp, map_sum]
    simp only [MvPolynomial.eval_monomial, formEvalR, veronese]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    congr 1
    rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
    simp only [Mon.toFinsupp, Finsupp.equivFunOnFinite_symm_apply_apply]
  by_contra h
  push Not at h
  exact hpne (MvPolynomial.funext (fun x => by rw [heval x, h x]; simp))

end Work.HP.HP2
