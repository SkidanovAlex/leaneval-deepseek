import Mathlib
import Submission.Work.WilE7.Defs

namespace Work.WilE7

theorem poly_bound (b : MvPolynomial (Fin 2) ℕ) :
    (∃ p : Polynomial ℕ, ∀ D : ℕ, p.eval D = b.eval ![D, D]) ∧
    (∃ p : Polynomial ℕ, ∀ D : ℕ, p.eval D = b.eval ![D, D + 1]) ∧
    (∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ, b.eval ![D, k * (D + 1)] = b'.eval ![D, k]) ∧
    (∀ D k k' : ℕ, k ≤ k' → b.eval ![D, k] ≤ b.eval ![D, k']) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Substitute `X₀ ↦ X`, `X₁ ↦ X`: the diagonal `D ↦ b(D,D)` is a polynomial in `D`.
    refine ⟨MvPolynomial.aeval (fun _ : Fin 2 => Polynomial.X) b, fun D => ?_⟩
    rw [← Polynomial.coe_aeval_eq_eval]
    rw [MvPolynomial.comp_aeval_apply (fun _ : Fin 2 => Polynomial.X) (Polynomial.aeval D) b]
    simp only [Polynomial.aeval_X]
    rw [MvPolynomial.aeval_eq_eval]
    rw [show (fun _ : Fin 2 => D) = ![D, D] from by funext i; fin_cases i <;> rfl]
  · -- Substitute `X₀ ↦ X`, `X₁ ↦ X + 1`: the line `D ↦ b(D, D+1)` is a polynomial in `D`.
    refine ⟨MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (Polynomial.X : Polynomial ℕ)
      else (Polynomial.X + 1)) b, fun D => ?_⟩
    rw [← Polynomial.coe_aeval_eq_eval]
    rw [MvPolynomial.comp_aeval_apply (fun i : Fin 2 => if i = 0 then (Polynomial.X : Polynomial ℕ)
      else (Polynomial.X + 1)) (Polynomial.aeval D) b]
    rw [show (fun i : Fin 2 => Polynomial.aeval D (if i = 0 then (Polynomial.X : Polynomial ℕ)
        else (Polynomial.X + 1))) = ![D, D + 1] from by funext i; fin_cases i <;> simp]
    rw [MvPolynomial.aeval_eq_eval]
  · -- Substitute `X₀ ↦ X₀`, `X₁ ↦ X₁ * (X₀ + 1)`: the `D`-dependent change of variable
    -- `k ↦ k * (D + 1)` is realised by a polynomial in `(D, k)` with coefficients in `ℕ`.
    set f3 : Fin 2 → MvPolynomial (Fin 2) ℕ :=
      fun i => if i = 0 then MvPolynomial.X 0 else MvPolynomial.X 1 * (MvPolynomial.X 0 + 1) with hf3
    refine ⟨MvPolynomial.aeval f3 b, fun D k => ?_⟩
    have h1 : (fun i : Fin 2 => MvPolynomial.aeval ![D, k] (f3 i)) = ![D, k * (D + 1)] := by
      rw [hf3]
      funext i
      fin_cases i <;> simp
    rw [show MvPolynomial.eval ![D, k] (MvPolynomial.aeval f3 b)
          = MvPolynomial.aeval ![D, k] (MvPolynomial.aeval f3 b) from rfl]
    rw [MvPolynomial.comp_aeval_apply f3 (MvPolynomial.aeval ![D, k]) b]
    rw [h1, MvPolynomial.aeval_eq_eval]
  · -- Monotonicity: `b` has coefficients in `ℕ`, so it is a sum of monomials with
    -- non-negative coefficients, each of which is monotone in `k`.
    induction b using MvPolynomial.induction_on with
    | C a => intro D k k' _; simp
    | add p q hp hq =>
        intro D k k' h
        rw [map_add, map_add]
        exact Nat.add_le_add (hp D k k' h) (hq D k k' h)
    | mul_X p i hp =>
        intro D k k' h
        rw [map_mul, map_mul]
        exact Nat.mul_le_mul (hp D k k' h) (by fin_cases i <;> simp [h])

end Work.WilE7
