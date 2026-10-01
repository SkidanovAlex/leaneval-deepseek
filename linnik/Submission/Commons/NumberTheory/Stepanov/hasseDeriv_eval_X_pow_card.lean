import Mathlib.FieldTheory.Finite.Basic
import Submission.Commons.Algebra.Polynomial.hasseDeriv_mul_X_pow_prime_pow

namespace Commons.NumberTheory.Stepanov

open Polynomial

/-- **Hasse derivatives commute with the Frobenius substitution `Y ↦ X ^ #F`.**
Writing `A ∈ F[X][Y]` as a polynomial in `Y` with coefficients in `F[X]`, the `ℓ`-th Hasse
derivative (in `X`) of the specialized polynomial `A(X, X ^ #F)` equals the specialization of
the polynomial obtained by applying the `ℓ`-th Hasse derivative to every coefficient of `A`.
The bound `ℓ < #F` is what makes the Frobenius part (`Y = X ^ #F`) drop out: for `F` of
characteristic `p` and `q = p ^ h = #F`, one has `(X + Z) ^ q = X ^ q + Z ^ q`, so the Hasse
derivative only sees the `X`-direction as long as `ℓ < q`. -/
theorem hasseDeriv_eval_X_pow_card {F : Type*} [Field F] [Fintype F]
    (A : Polynomial (Polynomial F)) (ℓ : ℕ) (hℓ : ℓ < Fintype.card F) :
    Polynomial.hasseDeriv ℓ (A.eval (Polynomial.X ^ Fintype.card F))
      = (A.sum (fun j a => Polynomial.monomial j (Polynomial.hasseDeriv ℓ a))).eval
          (Polynomial.X ^ Fintype.card F) := by
  classical
  -- Write `#F = p ^ h` with `p = ringChar F` the characteristic of `F`.
  obtain ⟨h, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hℓ' : ℓ < ringChar F ^ (h : ℕ) := by rw [← hcard]; exact hℓ
  -- The core vanishing: for `ℓ < #F`, the Hasse derivative of `c * (X ^ #F) ^ n` is
  -- `hasseDeriv ℓ c * (X ^ #F) ^ n`, because all lower Hasse derivatives of `(X ^ #F) ^ n`
  -- vanish in characteristic `p` (`(X ^ #F) ^ n = X ^ (n * p ^ h)`).
  have hterm : ∀ (a : Polynomial F) (n : ℕ),
      Polynomial.hasseDeriv ℓ (a * (Polynomial.X ^ Fintype.card F) ^ n)
        = Polynomial.hasseDeriv ℓ a * (Polynomial.X ^ Fintype.card F) ^ n := by
    intro a n
    have hpow : ((Polynomial.X : Polynomial F) ^ Fintype.card F) ^ n
        = (Polynomial.X : Polynomial F) ^ (n * ringChar F ^ (h : ℕ)) := by
      rw [← pow_mul, hcard, Nat.mul_comm]
    have hkey := Commons.Algebra.Polynomial.hasseDeriv_mul_X_pow_prime_pow
      (ringChar F) (h : ℕ) hp ℓ n hℓ' a
    rw [← hpow] at hkey
    exact hkey
  -- Expand `A` into monomials and use additivity of everything involved.
  refine Polynomial.induction_on' A ?add ?mono
  · intro p r hp' hr'
    have hsum : (p + r).sum (fun j a => Polynomial.monomial j (Polynomial.hasseDeriv ℓ a))
        = p.sum (fun j a => Polynomial.monomial j (Polynomial.hasseDeriv ℓ a))
          + r.sum (fun j a => Polynomial.monomial j (Polynomial.hasseDeriv ℓ a)) :=
      Polynomial.sum_add_index p r _ (fun i => by simp)
        (fun a b1 b2 => by simp)
    rw [Polynomial.eval_add, map_add, hsum, Polynomial.eval_add, hp', hr']
  · intro n a
    rw [Polynomial.sum_monomial_index a
      (fun j a => Polynomial.monomial j (Polynomial.hasseDeriv ℓ a)) (by simp)]
    simp only [Polynomial.eval_monomial]
    exact hterm a n

end Commons.NumberTheory.Stepanov