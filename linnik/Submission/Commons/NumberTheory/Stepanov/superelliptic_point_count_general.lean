import Mathlib
import Submission.Commons.NumberTheory.Stepanov.superelliptic_point_count_bound
import Submission.Commons.NumberTheory.Stepanov.ncard_points_superelliptic

/-!
# Stepanov's elementary bound for the superelliptic curve `y ^ e = g x` (general form)

Target (`Commons.NumberTheory.Stepanov.superelliptic_point_count_general`):

```
∃ C : ℝ, 0 < C ∧ ∀ {F} [Field F] [Fintype F], e ∣ Fintype.card F - 1 →
  ∀ g : F[X], g.natDegree ≤ d →
  (∀ p, p.Prime → p ∣ e → ∀ a h, g ≠ C a * h ^ p) →
  #{(p : F × F) | p.2 ^ e = g.eval p.1} ≤ #F + C * √(#F)
```

The mathematical content (the Stepanov/Hasse bound `#S ≤ #F + C √#F` for the Kummer cover
`y ^ e = g x`, uniformly in the finite field, with `C` depending only on `e` and `deg g`) is
established in the shared commons:

* `Commons.NumberTheory.Stepanov.ncard_points_superelliptic` — the exact count
  `#S = e * T + R₀`, `T = #{a | g a ^ ((q-1)/e) = 1}`, `R₀ = #{a | g a = 0}`;
* `Commons.NumberTheory.Stepanov.superelliptic_char_sum_bound` — Stepanov's bound
  `T ≤ #F / e + C √#F` (elementary method: a Hasse-derivative auxiliary polynomial in the
  Kummer ring `F[X][Y]/(Y^e - g(X))`, with the non-degeneracy coming from the hypothesis);
* `Commons.NumberTheory.Stepanov.superelliptic_point_count_bound` — the two combined, which is
  exactly the target statement except that it carries a `[DecidableEq F]` hypothesis (needed
  internally for the Frobenius-ideal bookkeeping).  Since `DecidableEq F` is available
  classically for any finite type, the requested statement (which omits it) follows directly.
-/

namespace Commons.NumberTheory.Stepanov

open Polynomial

/-- **Stepanov's bound for the superelliptic point count** `y ^ e = g x`, uniform in the field:
for fixed `e ≥ 2` and `d ≥ 1` there is `C > 0` with
`#{(x,y) ∈ F × F | y ^ e = g x} ≤ #F + C √#F` for every finite field `F` with `e ∣ #F - 1` and
every `g ∈ F[X]` of degree `≤ d` that is not a constant multiple of a `p`-th power for any prime
`p ∣ e`. -/
theorem superelliptic_point_count_general (e d : ℕ) (he : 2 ≤ e) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : Type*} [Field F] [Fintype F], e ∣ Fintype.card F - 1 →
      ∀ (g : Polynomial F), g.natDegree ≤ d →
      (∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
        g ≠ Polynomial.C a * h ^ p) →
      (({p : F × F | p.2 ^ e = g.eval p.1} : Set (F × F)).ncard : ℝ) ≤
        (Fintype.card F : ℝ) + C * Real.sqrt (Fintype.card F) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := superelliptic_point_count_bound e d he hd
  exact ⟨C, hCpos, fun {F} _ _ hdiv g hgd hnd => hC F hdiv g hgd hnd⟩

end Commons.NumberTheory.Stepanov
