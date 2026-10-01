import Mathlib
import Submission.Commons.NumberTheory.Stepanov.superelliptic_point_count_general
import Submission.Commons.NumberTheory.Stepanov.not_const_mul_pow_of_irreducible

open Polynomial

/-!
# Stepanov's elementary bound for the superelliptic curve `y ^ e = f x`

`Commons.NumberTheory.Stepanov.superelliptic_point_count` : for `e ≥ 2`, `d ≥ 1` there is
`C > 0`, depending only on `e` and `d`, such that for every finite field `F` with `e ∣ #F - 1`
and every nonzero monic `f ∈ F[X]` of degree `≤ d` with `X ^ e - f` irreducible over `F[X]`,

`#{(x, y) : F × F | y ^ e = f x} ≤ #F + C √(#F)`.

The mathematical content is Stepanov's (Bombieri's) elementary method, and it lives in the
shared commons:

* `Commons.NumberTheory.Stepanov.ncard_points_superelliptic` — the exact decomposition
  `#S = e · T + R₀`, `T = #{x | f x ^ ((#F-1)/e) = 1}`, `R₀ = #{x | f x = 0}`;
* `Commons.NumberTheory.Stepanov.superelliptic_char_sum_bound` — Stepanov's bound
  `T ≤ #F / e + C √#F`, via an auxiliary polynomial built from Hasse derivatives in the
  Kummer ring `F[X][Y]/(Y ^ e - f(X))`, with the non-degeneracy input supplied by the
  hypothesis `(∀ p prime, p ∣ e → ∀ a h, f ≠ C a * h ^ p)`;
* `Commons.NumberTheory.Stepanov.superelliptic_point_count_general` — the two combined,
  stated for this non-degeneracy hypothesis rather than for irreducibility of `X ^ e - C f`;
* `Commons.NumberTheory.Stepanov.not_const_mul_pow_of_irreducible` — the Kummer-theoretic
  transfer which derives the non-degeneracy hypothesis from the irreducibility hypothesis of
  the present statement (via Gauss's lemma and `pow_ne_of_irreducible_X_pow_sub_C`).

This file simply assembles those four into the requested statement.
-/

namespace Commons.NumberTheory.Stepanov

open Polynomial

/-- Stepanov's elementary bound for the number of points on the curve `y ^ e = f x`
over a finite field, uniform in the field and with a constant depending only on `e`
and `deg f` (so it can be iterated over all extension fields `F_{q^ν}`).
The standard shape is `#C(F) ≤ |F| + C(e d) √|F|`; the proof is Stepanov's /
Bombieri's elementary method, which avoids the Riemann hypothesis for curves. -/
theorem superelliptic_point_count (e d : ℕ) (he : 2 ≤ e) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : Type*} [Field F] [Fintype F], e ∣ Fintype.card F - 1 →
      ∀ (f : Polynomial F), f ≠ 0 → f.natDegree ≤ d → f.Monic →
      Irreducible (Polynomial.X ^ e - Polynomial.C f) →
      (({p : F × F | p.2 ^ e = f.eval p.1}.ncard : ℝ) ≤
        (Fintype.card F : ℝ) + C * Real.sqrt (Fintype.card F)) := by
  obtain ⟨C, hCpos, hC⟩ := superelliptic_point_count_general e d he hd
  refine ⟨C, hCpos, ?_⟩
  intro F _ _ hdiv f hf0 hfdeg hfmon hirr
  exact hC (F := F) hdiv f hfdeg
    (not_const_mul_pow_of_irreducible e he f hf0 hfmon hirr)

end Commons.NumberTheory.Stepanov
