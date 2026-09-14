import Mathlib
import Submission.Subspace.RothIndex

/-!
# Polynomials in the first `n + 1` variables and the `Fin.succ` embedding

For the Wronskian of Roth's lemma one writes a polynomial
`P ∈ K[x_0,…,x_n]` as `∑_r Φ_r Ψ_r` where `Φ_r` involves only `x_1,…,x_n` (i.e. lies in the
image of `MvPolynomial.rename Fin.succ`) and `Ψ_r` only `x_0`.  The key elementary facts are
that partial derivatives in the "missing" variables annihilate `Φ_r` and `Ψ_r`; these are
recorded here in a general form.
-/

open scoped BigOperators

namespace Submission.Subspace

variable {R : Type*} [CommSemiring R] {σ τ : Type*}

/-- A partial derivative in a variable that does not occur annihilates any polynomial: if
`i ∉ Set.range f` then `∂_i (rename f P) = 0`. -/
lemma pderiv_rename_eq_zero (f : σ → τ) (i : τ) (hi : i ∉ Set.range f)

    (P : MvPolynomial σ R) : MvPolynomial.pderiv i (MvPolynomial.rename f P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p k hp =>
      have hk : f k ≠ i := fun h => hi ⟨k, h⟩
      have hsplit : (MvPolynomial.rename f) (p * MvPolynomial.X k)
          = (MvPolynomial.rename f) p * MvPolynomial.X (f k) := by
        rw [map_mul, MvPolynomial.rename_X]
      rw [hsplit, MvPolynomial.pderiv_mul, hp, MvPolynomial.pderiv_X_of_ne hk]
      simp

