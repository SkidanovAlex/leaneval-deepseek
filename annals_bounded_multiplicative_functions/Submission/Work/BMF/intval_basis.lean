import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The binomial basis of the integer-valued polynomials

`binP j` is the polynomial `X (X-1) ⋯ (X-j+1) / j! = C(X, j)`, the `j`-th binomial-coefficient
polynomial.  We record the elementary facts needed for the Bézout decomposition of an
integer-valued polynomial: evaluation at naturals, degree, and the Pascal identity
`Δ binP (j+1) = binP j`.
-/

namespace Work.BMF

open Polynomial Finset

/-- The binomial-coefficient polynomial `C(X, j) = X(X-1)⋯(X-j+1)/j!`. -/
noncomputable def binP (j : ℕ) : ℝ[X] := C ((j.factorial : ℝ)⁻¹) * descPochhammer ℝ j

theorem binP_zero : binP 0 = 1 := by
  simp [binP]

theorem binP_eval_nat (j n : ℕ) : eval (n : ℝ) (binP j) = (n.choose j : ℝ) := by
  have hfac : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hD : eval (n : ℝ) (descPochhammer ℝ j) = (n.choose j : ℝ) * (j.factorial : ℝ) := by
    rw [Nat.cast_choose_eq_descPochhammer_div ℝ n j]
    field_simp
  rw [binP, eval_mul, eval_C, hD, mul_comm ((n.choose j : ℝ)) ((j.factorial : ℝ)),
    ← mul_assoc, inv_mul_cancel₀ hfac, one_mul]

theorem binP_natDegree (j : ℕ) : (binP j).natDegree = j := by
  have hfac : ((j.factorial : ℝ))⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero j)
  rw [binP, natDegree_C_mul hfac, descPochhammer_natDegree]

theorem binP_natDegree_le (j : ℕ) : (binP j).natDegree ≤ j := (binP_natDegree j).le

/-- The Pascal identity in the form used by the Newton expansion: the first difference of
`C(X, j+1)` is `C(X, j)`. -/
theorem binP_comp_succ (j : ℕ) :
    (binP (j + 1)).comp (X + C 1) = binP (j + 1) + binP j := by
  have hroot : ∀ n : ℕ,
      eval (n : ℝ) ((binP (j + 1)).comp (X + C 1) - binP (j + 1) - binP j) = 0 := by
    intro n
    simp only [eval_sub, eval_comp, eval_add, eval_X, eval_C]
    have h1 : eval ((n : ℝ) + 1) (binP (j + 1)) = ((n + 1).choose (j + 1) : ℝ) := by
      rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, binP_eval_nat]
    rw [h1, binP_eval_nat, binP_eval_nat, Nat.choose_succ_succ']
    push_cast
    ring
  have hD : (binP (j + 1)).comp (X + C 1) - binP (j + 1) - binP j = 0 := by
    apply eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective (Nat.cast_injective)).mono
    rintro x ⟨n, rfl⟩
    exact hroot n
  linear_combination hD

/-- The first difference lowers the degree by one: applied to a polynomial of degree `≤ k+1`,
`P(X+1) - P(X)` has degree `≤ k`. -/
theorem natDegree_comp_X_add_one_sub_le {γ : ℝ[X]} {k : ℕ} (hγ : γ.natDegree ≤ k + 1) :
    (γ.comp (X + C 1) - γ).natDegree ≤ k := by
  by_cases h0 : γ = 0
  · rw [h0]; simp
  have hqc : (0 : WithBot ℕ) < (X + C 1 : ℝ[X]).degree := by
    rw [degree_X_add_C]; exact WithBot.coe_lt_coe.mpr (by norm_num)
  have hdeg_eq : (γ.comp (X + C 1)).degree = γ.degree := by
    rw [degree_comp hqc, degree_X_add_C, mul_one]
  have hne : γ.comp (X + C 1) ≠ 0 := by
    intro h
    rw [h, degree_zero] at hdeg_eq
    exact h0 (Polynomial.degree_eq_bot.mp hdeg_eq.symm)
  have hlc : (γ.comp (X + C 1)).leadingCoeff = γ.leadingCoeff := by
    rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; norm_num), leadingCoeff_X_add_C,
      one_pow, mul_one]
  have hlt : (γ.comp (X + C 1) - γ).degree < γ.degree := by
    rw [← hdeg_eq]; exact Polynomial.degree_sub_lt_left hdeg_eq hne hlc
  have hle : γ.degree ≤ ((k + 1 : ℕ) : WithBot ℕ) := natDegree_le_iff_degree_le.mp hγ
  have hlt2 : (γ.comp (X + C 1) - γ).degree < ((k + 1 : ℕ) : WithBot ℕ) := lt_of_lt_of_le hlt hle
  by_cases hD : γ.comp (X + C 1) - γ = 0
  · rw [hD]; simp
  · have := (natDegree_lt_iff_degree_lt hD).mpr hlt2
    omega

end Work.BMF
