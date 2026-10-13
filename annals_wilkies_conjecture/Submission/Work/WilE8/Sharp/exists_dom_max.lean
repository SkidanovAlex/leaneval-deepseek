import Mathlib

/-!
# Domination for two-variable `ℕ`-polynomials with a shift in both coordinates

For a polynomial `b ∈ ℕ[X,Y]` and a constant `c`, we produce a single polynomial `b'` with
`b'(D, k) ≥ b(max D c, k+1)` for all `D k : ℕ`.

The construction is the substitution `X ↦ X + c`, `Y ↦ Y + 1`: with
`b' := bind₁ (X ↦ X + c, Y ↦ Y + 1) b` we have the *exact* identity
`b'(D,k) = b(D+c, k+1)`, and `max D c ≤ D + c` together with monotonicity of the
evaluation of a `ℕ`-coefficient polynomial concludes.
-/

namespace Work.WilE8.Sharp

/-- Evaluation of an `ℕ`-coefficient multivariate polynomial is monotone in the point:
if `x i ≤ y i` for all `i` then `b(x) ≤ b(y)`. -/
lemma eval_nat_mono_point (b : MvPolynomial (Fin 2) ℕ) {x y : Fin 2 → ℕ}
    (h : ∀ i, x i ≤ y i) : MvPolynomial.eval x b ≤ MvPolynomial.eval y b := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      rw [MvPolynomial.eval_add, MvPolynomial.eval_add]
      exact Nat.add_le_add hp hq
  | mul_X p i hp =>
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
      exact Nat.mul_le_mul hp (h i)

/-- The substitution `X ↦ X + c`, `Y ↦ Y + 1` intertwines the evaluation at `(D, k)` with the
evaluation at `(D + c, k + 1)`. -/
lemma eval_bind_shift_max (c : ℕ) (b : MvPolynomial (Fin 2) ℕ) (D k : ℕ) :
    MvPolynomial.eval ![D, k] (MvPolynomial.bind₁
      (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 + MvPolynomial.C c
                       else MvPolynomial.X 1 + 1) b)
      = MvPolynomial.eval ![D + c, k + 1] b := by
  conv_lhs => rw [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  rw [MvPolynomial.eval]
  refine MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext i
  fin_cases i <;> simp

/-- **Domination with a shift.**  For every `c` and every `b ∈ ℕ[X,Y]` there is `b' ∈ ℕ[X,Y]`
with `b(max D c, k+1) ≤ b'(D, k)` for all `D, k : ℕ`. -/
theorem exists_dom_max (c : ℕ) (b : MvPolynomial (Fin 2) ℕ) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ,
      MvPolynomial.eval ![max D c, k + 1] b ≤ MvPolynomial.eval ![D, k] b' := by
  refine ⟨MvPolynomial.bind₁ (fun i : Fin 2 =>
    if i = 0 then MvPolynomial.X 0 + MvPolynomial.C c else MvPolynomial.X 1 + 1) b, ?_⟩
  intro D k
  rw [eval_bind_shift_max c b D k]
  refine eval_nat_mono_point b ?_
  intro i
  fin_cases i
  · exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  · simp

end Work.WilE8.Sharp
