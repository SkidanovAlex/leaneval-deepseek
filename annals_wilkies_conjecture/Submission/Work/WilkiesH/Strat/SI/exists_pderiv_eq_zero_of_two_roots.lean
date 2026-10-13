import Mathlib

/-!
# Two roots of a multivariate polynomial force a root of a partial derivative

Given a multivariate polynomial `P` in `k + 1` variables over `ℝ`, a point `u : Fin k → ℝ` and two
real numbers `a < b` such that the one-variable polynomial `t ↦ P(u, t)` vanishes at `a` and at `b`,
Rolle's theorem produces `c ∈ (a, b)` at which the derivative of this one-variable polynomial
vanishes; the latter is `t ↦ (∂P/∂x_k)(u, t)`.

The reduction to a univariate polynomial is done by the algebra homomorphism
`MvPolynomial.aeval (psi k u) : MvPolynomial (Fin (k+1)) ℝ →ₐ[ℝ] Polynomial ℝ` that sends the last
variable to `Polynomial.X` and the first `k` variables to the constants `C (u j)`; the two helper
lemmas below record that this homomorphism commutes with evaluation (at `t` and along `Fin.snoc u t`)
and with the formal derivatives `Polynomial.derivative` and `MvPolynomial.pderiv (Fin.last k)`.
-/

namespace Work.WilkiesH.Strat.SI

/-- Assignment of variables realizing `P ↦ P(u, X)`: the last variable goes to `Polynomial.X`, the
others to the constants `C (u j)`. -/
private noncomputable def psi (k : ℕ) (u : Fin k → ℝ) : Fin (k + 1) → Polynomial ℝ :=
  Fin.snoc (fun j => Polynomial.C (u j)) Polynomial.X

private lemma eval_psi (k : ℕ) (u : Fin k → ℝ) (t : ℝ) (i : Fin (k + 1)) :
    (psi k u i).eval t = (Fin.snoc u t : Fin (k + 1) → ℝ) i := by
  cases i using Fin.lastCases <;> simp [psi]

/-- Evaluating `P` at `Fin.snoc u t` equals evaluating the univariate polynomial `P(u, X)` at `t`. -/
private lemma eval_aeval_psi (k : ℕ) (u : Fin k → ℝ) (P : MvPolynomial (Fin (k + 1)) ℝ) (t : ℝ) :
    (MvPolynomial.aeval (psi k u) P).eval t = MvPolynomial.eval (Fin.snoc u t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [psi, Polynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, Polynomial.eval_mul, hp, eval_psi,
        MvPolynomial.eval_X]

/-- The homomorphism `P ↦ P(u, X)` commutes with formal differentiation in the last variable. -/
private lemma deriv_aeval_psi (k : ℕ) (u : Fin k → ℝ) (P : MvPolynomial (Fin (k + 1)) ℝ) :
    Polynomial.derivative (MvPolynomial.aeval (psi k u) P) =
      MvPolynomial.aeval (psi k u) (MvPolynomial.pderiv (Fin.last k) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [psi, Polynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      cases i using Fin.lastCases with
      | last =>
          have hlast : psi k u (Fin.last k) = Polynomial.X := by simp [psi]
          simp only [map_mul, MvPolynomial.aeval_X, hlast, Polynomial.derivative_mul,
            Polynomial.derivative_X, mul_one, hp, MvPolynomial.pderiv_mul,
            MvPolynomial.pderiv_X_self, map_add]
      | cast j =>
          have hxj : MvPolynomial.pderiv (Fin.last k)
              (MvPolynomial.X j.castSucc : MvPolynomial (Fin (k + 1)) ℝ) = 0 :=
            MvPolynomial.pderiv_X_of_ne (Fin.castSucc_ne_last j)
          have hcast : psi k u j.castSucc = Polynomial.C (u j) := by simp [psi]
          simp only [MvPolynomial.pderiv_mul, hxj, map_mul, MvPolynomial.aeval_X, hcast,
            Polynomial.derivative_mul, Polynomial.derivative_C, mul_zero, add_zero, hp]

theorem exists_pderiv_eq_zero_of_two_roots {k : ℕ} (P : MvPolynomial (Fin (k + 1)) ℝ) (u : Fin k → ℝ)
    {a b : ℝ} (hab : a < b) (ha : MvPolynomial.eval (Fin.snoc u a) P = 0)
    (hb : MvPolynomial.eval (Fin.snoc u b) P = 0) :
    ∃ c ∈ Set.Ioo a b, MvPolynomial.eval (Fin.snoc u c) (MvPolynomial.pderiv (Fin.last k) P) = 0 := by
  set Q : Polynomial ℝ := MvPolynomial.aeval (psi k u) P with hQ
  have hcont : ContinuousOn (fun t => MvPolynomial.eval (Fin.snoc u t) P) (Set.Icc a b) :=
    (Polynomial.continuousOn Q).congr fun t _ => by
      rw [hQ]; exact (eval_aeval_psi k u P t).symm
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun t => MvPolynomial.eval (Fin.snoc u t) P)
        (MvPolynomial.eval (Fin.snoc u x) (MvPolynomial.pderiv (Fin.last k) P)) x := by
    intro x _
    have h := Polynomial.hasDerivAt Q x
    have key1 : (fun y : ℝ => Q.eval y) = fun t => MvPolynomial.eval (Fin.snoc u t) P := by
      funext t; rw [hQ]; exact eval_aeval_psi k u P t
    have key2 : Q.derivative.eval x =
        MvPolynomial.eval (Fin.snoc u x) (MvPolynomial.pderiv (Fin.last k) P) := by
      rw [hQ, deriv_aeval_psi k u P]
      exact eval_aeval_psi k u (MvPolynomial.pderiv (Fin.last k) P) x
    rw [key1, key2] at h
    exact h
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab hcont (by rw [ha, hb]) hderiv
  exact ⟨c, hc, hc0⟩

end Work.WilkiesH.Strat.SI
