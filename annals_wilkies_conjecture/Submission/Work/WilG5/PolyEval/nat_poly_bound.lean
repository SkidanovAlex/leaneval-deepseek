import Mathlib

namespace Work.WilG5.PolyEval

/-- Any multivariate polynomial with natural coefficients, evaluated at natural
points, grows at most polynomially in `1 + ∑ i, x i`.

The proof is by induction on the polynomial (`MvPolynomial.induction_on`): the
claim is closed under constants, addition and multiplication by a variable.
The bounding quantity `S x = 1 + ∑ i, (x i : ℝ)` satisfies `S x ≥ 1`, and each
coordinate `x i` is `≤ S x`; these two facts are all that is needed. -/
theorem nat_poly_bound {m : ℕ} (b : MvPolynomial (Fin m) ℕ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ x : Fin m → ℕ,
      (b.eval x : ℝ) ≤ C * (1 + ∑ i, (x i : ℝ)) ^ N := by
  classical
  let S : (Fin m → ℕ) → ℝ := fun x => 1 + ∑ i, (x i : ℝ)
  have hS1 : ∀ x, 1 ≤ S x := by
    intro x
    simp only [S]
    have h : 0 ≤ ∑ i, (x i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    linarith
  suffices H : ∀ b : MvPolynomial (Fin m) ℕ,
      ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ x : Fin m → ℕ, (b.eval x : ℝ) ≤ C * S x ^ N by
    exact H b
  intro b
  induction b using MvPolynomial.induction_on with
  | C a =>
      refine ⟨(a : ℝ), 0, Nat.cast_nonneg a, ?_⟩
      intro x
      simp [S]
  | add p q hp hq =>
      obtain ⟨C1, N1, hC1, h1⟩ := hp
      obtain ⟨C2, N2, hC2, h2⟩ := hq
      refine ⟨C1 + C2, max N1 N2, by positivity, ?_⟩
      intro x
      have hSx : 1 ≤ S x := hS1 x
      have hSp : 0 ≤ S x := by linarith
      have e1 : S x ^ N1 ≤ S x ^ (max N1 N2) := pow_le_pow_right₀ hSx (le_max_left _ _)
      have e2 : S x ^ N2 ≤ S x ^ (max N1 N2) := pow_le_pow_right₀ hSx (le_max_right _ _)
      calc (MvPolynomial.eval x (p + q) : ℝ)
          = (MvPolynomial.eval x p : ℝ) + (MvPolynomial.eval x q : ℝ) := by
            simp [MvPolynomial.eval_add]
        _ ≤ C1 * S x ^ N1 + C2 * S x ^ N2 := add_le_add (h1 x) (h2 x)
        _ ≤ C1 * S x ^ (max N1 N2) + C2 * S x ^ (max N1 N2) :=
            add_le_add (mul_le_mul_of_nonneg_left e1 hC1) (mul_le_mul_of_nonneg_left e2 hC2)
        _ = (C1 + C2) * S x ^ (max N1 N2) := by ring
  | mul_X p n hp =>
      obtain ⟨C1, N1, hC1, h1⟩ := hp
      refine ⟨C1, N1 + 1, hC1, ?_⟩
      intro x
      have hSx : 1 ≤ S x := hS1 x
      have hSp : 0 ≤ S x := by linarith
      have hxn : (x n : ℝ) ≤ S x := by
        simp only [S]
        have h : (x n : ℝ) ≤ ∑ i, (x i : ℝ) :=
          Finset.single_le_sum (fun i _ => Nat.cast_nonneg (x i)) (Finset.mem_univ n)
        linarith
      calc (MvPolynomial.eval x (p * MvPolynomial.X n) : ℝ)
          = (MvPolynomial.eval x p : ℝ) * (x n : ℝ) := by
            simp [MvPolynomial.eval_mul]
        _ ≤ (C1 * S x ^ N1) * S x :=
            mul_le_mul (h1 x) hxn (Nat.cast_nonneg _) (mul_nonneg hC1 (pow_nonneg hSp N1))
        _ = C1 * S x ^ (N1 + 1) := by rw [pow_succ]; ring

end Work.WilG5.PolyEval
