import Mathlib
import Submission.Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le
import Submission.Commons.NumberTheory.NumberField.one_le_rootDiscr

/-!
# Last-mile assembly for Martinet's asymptotically-good totally real towers

Martinet's tower construction yields, for every `N`, a totally real number
field `K` of degree `d ≥ N` whose *root discriminant* is at most a fixed
constant `C` (`rootDiscr K ≤ C`).  The benchmark statement asks instead for
the absolute discriminant bound `|discr K| ≤ C ^ d`.  This module records the
(short) passage between the two formulations: from an unbounded-degree
totally-real family with bounded root discriminant we obtain the statement
`exists_totallyReal_discr_le` of `Challenge.lean`.

The whole mathematical content of Martinet's theorem is therefore reduced to
supplying the *family*: a constant `C > 0` such that for every `N` there is a
totally real number field of degree `≥ N` with root discriminant `≤ C`.
-/

open scoped NumberField
open NumberField

namespace Submission.Helpers

/-- From `rootDiscr K ≤ C` and `Module.finrank ℚ K = d`, we get the absolute
discriminant bound `|discr K| ≤ C ^ d`.

This is the (verified) shared-commons lemma
`Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le`. -/
theorem abs_discr_le_of_rootDiscr_le {K : Type*} [Field K] [NumberField K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) {C : ℝ}
    (hrd : NumberField.rootDiscr K ≤ C) : |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le hd hrd

/-- The root discriminant of any number field is at least one (shared-commons
`Commons.NumberTheory.NumberField.one_le_rootDiscr`), so it can serve as the
positive constant `C` of the tower. -/
theorem one_le_rootDiscr (K : Type*) [Field K] [NumberField K] :
    1 ≤ NumberField.rootDiscr K :=
  Commons.NumberTheory.NumberField.one_le_rootDiscr K

/-- The root-discriminant version of the benchmark statement: a constant
`C > 0` such that for every bound `N` there is a totally real number field
`K` of degree `≥ N` whose root discriminant is `≤ C`. -/
def rootDiscrFamily (C : ℝ) : Prop :=
  ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
      Module.finrank ℚ K = d ∧ NumberField.rootDiscr K ≤ C

/-- A root-discriminant-bounded family of totally real fields of unbounded
degree implies the benchmark statement. -/
theorem exists_totallyReal_discr_le_of_rootDiscrFamily
    (h : ∃ C : ℝ, 0 < C ∧ rootDiscrFamily C) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d := by
  rcases h with ⟨C, hC0, hfam⟩
  refine ⟨C, hC0, ?_⟩
  intro N
  rcases hfam N with ⟨d, hNd, K, instF, instNF, instTR, hd, hrd⟩
  refine ⟨d, hNd, K, instF, instNF, instTR, hd, ?_⟩
  exact abs_discr_le_of_rootDiscr_le (K := K) hd hrd

end Submission.Helpers
