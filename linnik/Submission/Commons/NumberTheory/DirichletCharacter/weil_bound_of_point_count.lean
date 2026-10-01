import Mathlib
import Submission.Commons.NumberTheory.CharacterSum.weil_bound_of_point_count

open Polynomial

namespace Commons.NumberTheory.DirichletCharacter

/-- The "L-function / Stepanov eigenvalue" step of Weil's bound: assuming the
(point-count form of the) Stepanov bound over all finite fields, the character sum
of a multiplicative character against a polynomial `f` is bounded by
`(#distinct roots of f) * √|F|`.

This is exactly the statement proved by the team in the shared commons as
`Commons.NumberTheory.CharacterSum.weil_bound_of_point_count` (the L-function /
Stepanov eigenvalue argument: the character-sum L-function `∑_{h monic} χ (resultant h f) u ^ (deg h)`
is a polynomial of degree `< #distinct roots of f`, its power sums over the extensions
satisfy the point-count bound, whence its roots have norm `≤ √|F|`), so we reuse it. -/
theorem weil_bound_of_point_count (e d : ℕ) (he : 2 ≤ e) (hd : 1 ≤ d)
    (hpc : ∃ C : ℝ, 0 < C ∧ ∀ {F : Type*} [Field F] [Fintype F], e ∣ Fintype.card F - 1 →
      ∀ (f : Polynomial F), f ≠ 0 → f.natDegree ≤ d → f.Monic →
      Irreducible (Polynomial.X ^ e - Polynomial.C f) →
      (({p : F × F | p.2 ^ e = f.eval p.1}.ncard : ℝ) ≤
        (Fintype.card F : ℝ) + C * Real.sqrt ((Fintype.card F : ℕ) : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : Type*} [Field F] [Fintype F], e ∣ Fintype.card F - 1 →
      ∀ (χ : MulChar F ℂ), χ ≠ 1 → orderOf χ = e →
      ∀ (f : Polynomial F), f ≠ 0 → f.natDegree ≤ d → f.Monic →
      Irreducible (Polynomial.X ^ e - Polynomial.C f) →
      ‖∑ x : F, χ (f.eval x)‖ ≤
        ((f.rootSet (AlgebraicClosure F)).ncard : ℝ) * Real.sqrt ((Fintype.card F : ℕ) : ℝ) :=
  Commons.NumberTheory.CharacterSum.weil_bound_of_point_count e d he hd hpc

end Commons.NumberTheory.DirichletCharacter
