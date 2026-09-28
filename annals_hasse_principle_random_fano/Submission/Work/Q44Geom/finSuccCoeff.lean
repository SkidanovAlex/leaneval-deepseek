import Mathlib

/-!
# Coefficient of a substituted polynomial after setting one variable to a constant

For a homogeneous polynomial `F` in three variables of degree `d`, substituting the
first variable by a constant `c` (and shifting the remaining two variables) does not
change the coefficient of a monomial `X₀^{α 0} X₁^{α 1}` whose total degree `α 0 + α 1`
is at least `d`: all other monomials of `F` involve the first variable, so their
degree in the remaining variables is strictly smaller than `d ≤ α 0 + α 1`.
-/

namespace Work.Q44Geom

open MvPolynomial

/-- `finSuccEquiv` followed by evaluation of the polynomial variable at `C c` implements
the substitution `X 0 ↦ C c`, `X 1 ↦ X 0`, `X 2 ↦ X 1`. -/
private lemma aeval_finSucc_eq (F : MvPolynomial (Fin 3) ℚ) (c : ℚ) :
    MvPolynomial.aeval (fun k : Fin 3 =>
        ![MvPolynomial.C c, MvPolynomial.X 0, MvPolynomial.X 1] k) F
      = Polynomial.eval (MvPolynomial.C c) (MvPolynomial.finSuccEquiv ℚ 2 F) := by
  have hX : ∀ n : Fin 3,
      (MvPolynomial.aeval (fun k : Fin 3 =>
          ![MvPolynomial.C c, MvPolynomial.X 0, MvPolynomial.X 1] k)
        (MvPolynomial.X n : MvPolynomial (Fin 3) ℚ))
        = Polynomial.eval (MvPolynomial.C c)
            (MvPolynomial.finSuccEquiv ℚ 2 (MvPolynomial.X n : MvPolynomial (Fin 3) ℚ)) := by
    intro n
    induction n using Fin.cases with
    | zero => simp [MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval_X]
    | succ j =>
      rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.eval_C, MvPolynomial.aeval_X]
      fin_cases j <;> simp
  induction F using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply, Polynomial.eval_C]
  | add p q hp hq => rw [map_add, map_add, Polynomial.eval_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, Polynomial.eval_mul, hp, hX n]

/-- The total degree of `Finsupp.cons i A` is `i` plus the total degree of `A`. -/
private lemma degree_cons (A : Fin 2 →₀ ℕ) (i : ℕ) :
    (Finsupp.cons i A).degree = i + A.degree := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three, Finsupp.degree_eq_sum, Fin.sum_univ_two]
  rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from Fin.succ_zero_eq_one.symm,
      show (2 : Fin 3) = Fin.succ (1 : Fin 2) from Fin.succ_one_eq_two.symm,
      Finsupp.cons_zero, Finsupp.cons_succ, Finsupp.cons_succ]
  ring

/-- The coefficient of `X₀^{A 0} X₁^{A 1}` in `F(C c, X₀, X₁)` is the sum over the
`X₀`-degree `i` of the coefficient of `X₀^i X₀^{A 0} X₁^{A 1}` in `F`, weighted by `c ^ i`. -/
private lemma coeff_aeval_finSucc (F : MvPolynomial (Fin 3) ℚ) (c : ℚ) (A : Fin 2 →₀ ℕ) :
    (MvPolynomial.aeval (fun k : Fin 3 =>
        ![MvPolynomial.C c, MvPolynomial.X 0, MvPolynomial.X 1] k) F).coeff A
      = ∑ i ∈ (MvPolynomial.finSuccEquiv ℚ 2 F).support,
          F.coeff (Finsupp.cons i A) * c ^ i := by
  rw [aeval_finSucc_eq, Polynomial.eval_eq_sum, Polynomial.sum_def, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← MvPolynomial.C_pow,
    mul_comm ((MvPolynomial.finSuccEquiv ℚ 2 F).coeff i) (MvPolynomial.C (c ^ i)),
    MvPolynomial.coeff_C_mul, MvPolynomial.finSuccEquiv_coeff_coeff]
  ring

theorem finSuccCoeff (F : MvPolynomial (Fin 3) ℚ) (d : ℕ) (hF : F.IsHomogeneous d)
    (c : ℚ) (α : Fin 2 → ℕ) (hα : d ≤ α 0 + α 1) :
    (MvPolynomial.aeval (fun k : Fin 3 => ![MvPolynomial.C c, MvPolynomial.X 0, MvPolynomial.X 1] k) F).coeff
        (Finsupp.equivFunOnFinite.symm α)
      = (MvPolynomial.aeval (fun k : Fin 3 => ![0, MvPolynomial.X 0, MvPolynomial.X 1] k) F).coeff
        (Finsupp.equivFunOnFinite.symm α) := by
  set A : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm α with hA
  have hA0 : A 0 = α 0 := congrFun (Finsupp.coe_equivFunOnFinite_symm α) 0
  have hA1 : A 1 = α 1 := congrFun (Finsupp.coe_equivFunOnFinite_symm α) 1
  have hAdeg : A.degree = α 0 + α 1 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, hA0, hA1]
  have hz : (fun k : Fin 3 =>
        ![(0 : MvPolynomial (Fin 2) ℚ), MvPolynomial.X 0, MvPolynomial.X 1] k)
      = (fun k : Fin 3 =>
        ![MvPolynomial.C (0 : ℚ), MvPolynomial.X 0, MvPolynomial.X 1] k) := by
    funext k; fin_cases k <;> simp
  rw [coeff_aeval_finSucc F c A, hz, coeff_aeval_finSucc F 0 A]
  apply Finset.sum_congr rfl
  intro i _
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp
  · have hzero : F.coeff (Finsupp.cons i A) = 0 := by
      apply hF.coeff_eq_zero
      rw [degree_cons, hAdeg]
      omega
    rw [hzero, zero_mul, zero_mul]

end Work.Q44Geom
