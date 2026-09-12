import Mathlib
/-!
# Part-A foundations for `thm:adjust` (algebraic dual condition)

Small self-contained lemmas needed by the algebraic core of Smith's
`thm:adjust` (GON.tex): the dual condition for the coefficient basis
`Q_i = Q/(X - α_i)` of a squarefree integer polynomial.
-/

noncomputable section
open scoped BigOperators

namespace Submission.PartAFound

/-- A rational algebraic integer (over `ℤ`) is an integer.  Given `x : ℂ` which is
integral over `ℤ` and equals the image of a rational `q`, `x` is the image of an
integer. -/
theorem int_of_isIntegral_rat {x : ℂ} (hx : IsIntegral ℤ x) (hq : ∃ q : ℚ, (q : ℂ) = x) :
    ∃ z : ℤ, (z : ℂ) = x := by
  classical
  rcases hq with ⟨q, hq⟩
  have hqi : IsIntegral ℤ q := by
    refine (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ) (x := q)
      (hAB := FaithfulSMul.algebraMap_injective ℚ ℂ)).mp ?_
    simpa [hq] using hx
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff (R := ℤ) (K := ℚ)).mp
    (inferInstance : IsIntegrallyClosed ℤ) hqi
  refine ⟨z, ?_⟩
  rw [← hq]
  exact_mod_cast hz

end Submission.PartAFound
