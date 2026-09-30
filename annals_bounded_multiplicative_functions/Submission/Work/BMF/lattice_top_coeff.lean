import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

set_option linter.unusedVariables false

open Polynomial Finset

/-- Coefficient of `X^j` in the dilation `p ↦ p(c·X)`: it is `p.coeff j * c^j`. -/
private lemma comp_C_mul_X_coeff (p : ℝ[X]) (c : ℝ) (j : ℕ) :
    (p.comp (C c * X)).coeff j = p.coeff j * c ^ j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, hp, hq, coeff_add, add_mul]
  | monomial n a =>
      rw [monomial_comp]
      have hpow : ((C c * X) ^ n) = C (c ^ n) * X ^ n := by rw [mul_pow, Polynomial.C_pow]
      rw [hpow, ← mul_assoc, ← Polynomial.C_mul, coeff_C_mul_X_pow, coeff_monomial]
      by_cases hjn : j = n
      · subst hjn; simp
      · simp [hjn, Ne.symm hjn]

/-- The `j`-th forward difference of the evaluation of a polynomial of degree `≤ j` is the
constant function `j! * coeff j`. -/
private lemma fwdDiff_iter_coeff (P : ℝ[X]) {j : ℕ} (h : P.natDegree ≤ j) :
    (fwdDiff (1 : ℝ))^[j] P.eval = fun _ => P.coeff j * (j.factorial : ℝ) := by
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hlt]
    funext x
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
  · rw [← heq, Polynomial.fwdDiff_iter_degree_eq_factorial]
    funext x
    show P.leadingCoeff * ((P.natDegree).factorial : ℝ)
        = P.coeff P.natDegree * ((P.natDegree).factorial : ℝ)
    rw [Polynomial.leadingCoeff]

theorem lattice_top_coeff {j : ℕ} {D Qm : ℕ} (hD : 1 ≤ D) (hQm : 1 ≤ Qm) {G : ℝ[X]}
    (hdeg : G.natDegree ≤ j)
    (hint : ∀ n : ℤ, ∃ m : ℤ, (D : ℝ) * G.eval ((1 / (Qm : ℝ)) * n) = m) :
    ∃ m : ℤ, (D : ℝ) * (j.factorial : ℝ) * G.coeff j / (Qm : ℝ) ^ j = m := by
  classical
  set c : ℝ := 1 / (Qm : ℝ) with hc
  set P : ℝ[X] := C (D : ℝ) * G.comp (C c * X) with hP
  have hPeval : ∀ x : ℝ, P.eval x = (D : ℝ) * G.eval (c * x) := by
    intro x
    simp only [hP, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_X]
  have hPd : P.natDegree ≤ j := by
    rw [hP]
    calc (C (D : ℝ) * G.comp (C c * X)).natDegree
        ≤ (G.comp (C c * X)).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ G.natDegree * (C c * X).natDegree := Polynomial.natDegree_comp_le
      _ ≤ G.natDegree * 1 := by
            gcongr; simpa using Polynomial.natDegree_C_mul_le c X
      _ = G.natDegree := mul_one _
      _ ≤ j := hdeg
  have hPc : P.coeff j = (D : ℝ) * G.coeff j * c ^ j := by
    rw [hP, Polynomial.coeff_C_mul, comp_C_mul_X_coeff]
    ring
  have hval : ∀ k : ℕ, ∃ m : ℤ, P.eval (k : ℝ) = m := by
    intro k
    obtain ⟨m, hm⟩ := hint (k : ℤ)
    refine ⟨m, ?_⟩
    have harg : c * (k : ℝ) = (1 / (Qm : ℝ)) * (k : ℤ) := by
      rw [hc]; push_cast; ring
    rw [hPeval, harg]
    exact hm
  choose f hf using hval
  refine ⟨∑ k ∈ range (j + 1), (-1 : ℤ) ^ (j - k) * (j.choose k : ℤ) * f k, ?_⟩
  have hdiff : (fwdDiff (1 : ℝ))^[j] P.eval 0 = P.coeff j * (j.factorial : ℝ) := by
    have := congr_fun (fwdDiff_iter_coeff P hPd) 0
    simpa using this
  have hsum : (fwdDiff (1 : ℝ))^[j] P.eval 0
      = ((∑ k ∈ range (j + 1), (-1 : ℤ) ^ (j - k) * (j.choose k : ℤ) * f k : ℤ) : ℝ) := by
    rw [fwdDiff_iter_eq_sum_shift]
    trans ((∑ k ∈ range (j + 1),
        (((-1 : ℤ) ^ (j - k) * (j.choose k : ℤ) * f k : ℤ)) : ℝ))
    · apply Finset.sum_congr rfl
      intro k hk
      rw [zero_add, show k • (1 : ℝ) = (k : ℝ) by simp, hf k, zsmul_eq_mul]
      push_cast; ring
    · rw [← Int.cast_sum]
  have key : (D : ℝ) * (j.factorial : ℝ) * G.coeff j / (Qm : ℝ) ^ j
      = P.coeff j * (j.factorial : ℝ) := by
    rw [hPc, hc, one_div_pow, div_eq_mul_inv, one_div]
    ring
  rw [key, ← hdiff]
  exact hsum

end Work.BMF
