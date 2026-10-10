import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

theorem MvPolyAffineNotAssociated (L : Type) [Field L] (a b c d : L) (hac : a ≠ c) :
    ¬ Associated (MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1 + MvPolynomial.C b :
        MvPolynomial (Fin 2) L)
      (MvPolynomial.X 0 + MvPolynomial.C c * MvPolynomial.X 1 + MvPolynomial.C d :
        MvPolynomial (Fin 2) L) := by
  rintro ⟨u, hu⟩
  -- `hu : P * ↑u = Q`, and every unit of `MvPolynomial (Fin 2) L` is a nonzero constant.
  obtain ⟨r, -, hur⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin 2) L))).mp u.isUnit
  rw [hur] at hu
  rw [mul_comm] at hu
  -- `hu : C r * P = Q`
  -- Finsupp inequalities used to evaluate the `ite` conditions of `coeff_X` / `coeff_C`.
  have hs1 : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single (0 : Fin 2) 1 := by
    intro h
    have h1 : ((Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 1) = 1 := Finsupp.single_eq_same
    have h0 : ((Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 1) = 0 :=
      Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)
    rw [h] at h1
    rw [h0] at h1
    exact one_ne_zero h1.symm
  have hs1' : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 :=
    Ne.symm hs1
  have hs2 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (0 : Fin 2) 1 := by
    intro h
    have h0 : ((Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 0) = 1 := Finsupp.single_eq_same
    rw [← h] at h0
    have hz : ((0 : Fin 2 →₀ ℕ) 0) = 0 := by simp
    rw [hz] at h0
    exact one_ne_zero h0.symm
  have hs3 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 := by
    intro h
    have h0 : ((Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 1) = 1 := Finsupp.single_eq_same
    rw [← h] at h0
    have hz : ((0 : Fin 2 →₀ ℕ) 1) = 0 := by simp
    rw [hz] at h0
    exact one_ne_zero h0.symm
  -- compare the coefficient of `X 0`
  have h0 : r = 1 := by
    have hc := congrArg (fun p : MvPolynomial (Fin 2) L => p.coeff (Finsupp.single 0 1)) hu
    rw [MvPolynomial.coeff_C_mul] at hc
    simpa [MvPolynomial.coeff_X, MvPolynomial.coeff_add, MvPolynomial.coeff_one,
      MvPolynomial.coeff_C, hs1, hs2] using hc
  -- compare the coefficient of `X 1`
  have h1 : a = c := by
    have hc := congrArg (fun p : MvPolynomial (Fin 2) L => p.coeff (Finsupp.single 1 1)) hu
    rw [MvPolynomial.coeff_C_mul] at hc
    rw [h0, one_mul] at hc
    simpa [MvPolynomial.coeff_X, MvPolynomial.coeff_add, MvPolynomial.coeff_one,
      MvPolynomial.coeff_C, hs1', hs3] using hc
  exact hac h1

end Work.MotAS
