import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.weil_local_bound
import Submission.Commons.Algebra.Polynomial.mult_modEq_of_const_mul_pow

/-!
# The `Fin 3` "correlation" bound in the non-degenerate (good) case

`Commons.NumberTheory.DirichletCharacter.charCorrelation6_primeMod_good` bounds the
three-factor correlation

`∑ x, χ (∏ i, (x + a i)) * conj (χ (∏ i, (x + b i)))`

of a non-trivial Dirichlet character `χ` modulo a prime `p` by `6 * √p`, provided the
multiplicity patterns of `a` and `b` differ modulo `orderOf χ` at some point `x`.

Route: rewrite the correlation of the products of three linear factors as the correlation
`∑ x, (∏ i, χ (x + a i)) * (∏ i, conj (χ (x + b i)))` of the individual factors
(multiplicativity of `χ` and of complex conjugation), and apply the general local Weil bound
`weil_local_bound` with `r = 3` (which gives `2 * 3 * √p = 6 * √p`).  Its non-degeneracy
hypothesis — that `(∏ (X + C (a i))) * (∏ (X + C (b i)))^(orderOf χ - 1)` is not a constant
multiple of an `orderOf χ`-th power — is exactly the contrapositive of the multiplicity
congruence supplied by `mult_modEq_of_const_mul_pow`, so the hypothesis `hgood` yields it.
-/

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

theorem charCorrelation6_primeMod_good {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) (a b : Fin 3 → ZMod p)
    (hgood : ∃ x : ZMod p,
      (Finset.univ.filter (fun i : Fin 3 => a i = x)).card % orderOf χ
        ≠ (Finset.univ.filter (fun i : Fin 3 => b i = x)).card % orderOf χ) :
    ‖∑ x : ZMod p, χ (∏ i, (x + a i)) * (starRingEnd ℂ) (χ (∏ i, (x + b i)))‖
      ≤ 6 * Real.sqrt (p : ℝ) := by
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  -- The non-degeneracy hypothesis required by `weil_local_bound`, from `hgood`.
  have hgood_poly : ∀ (c : ZMod p) (Q : Polynomial (ZMod p)),
      (∏ i, (Polynomial.X + Polynomial.C (a i) : Polynomial (ZMod p))) *
        (∏ i, (Polynomial.X + Polynomial.C (b i) : Polynomial (ZMod p)))^(orderOf χ - 1)
      ≠ Polynomial.C c * Q^(orderOf χ) := by
    intro c Q hcon
    obtain ⟨x, hx⟩ := hgood
    exact hx (Commons.Algebra.Polynomial.mult_modEq_of_const_mul_pow hm2 a b hcon x)
  have hwb := weil_local_bound χ hχ 3 (by norm_num) a b hgood_poly
  -- Rewrite the product-correlation as the factor-wise correlation.
  have hsum_eq :
      (∑ x : ZMod p, (∏ i, χ (x + a i)) * (∏ i, (starRingEnd ℂ) (χ (x + b i))))
        = ∑ x : ZMod p,
            χ (∏ i, (x + a i)) * (starRingEnd ℂ) (χ (∏ i, (x + b i))) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_prod χ (fun i => x + a i) Finset.univ,
      map_prod χ (fun i => x + b i) Finset.univ,
      map_prod (starRingEnd ℂ) (fun i => χ (x + b i)) Finset.univ]
  rw [hsum_eq] at hwb
  refine hwb.trans (le_of_eq ?_)
  norm_num

end Commons.NumberTheory.DirichletCharacter
