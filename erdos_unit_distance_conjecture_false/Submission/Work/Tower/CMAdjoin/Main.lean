import Submission.Work.Tower.CMAdjoin.Basic
import Submission.Work.Tower.CMAdjoin.rootDiscr_cmAdjoin_le
import Submission.Work.Tower.CMAdjoin.splitsCompletely_cmAdjoin
import Submission.Work.Defs.Basic

/-!
# Adjoining `i` to a totally real field (paper Proposition 3.8, Step 4)

The last step of the class-field tower of *Planar Point Sets with Many Unit Distances*
(Erdős's unit-distance conjecture is false): every totally real number field `L` of large
degree and bounded root discriminant can be turned into a CM field `K = L(i)` whose root
discriminant is at most twice that of `L`, and in which the rational primes `q ≡ 1 (mod 4)`
that split completely in `L` still split completely.

## Main result

* `Work.Tower.exists_cm_adjoin`: given a totally real number field `L`, there is a field `K`
  with an `L`-algebra structure that is a CM number field, with `[K : L] = 2`,
  `[K : ℚ] = 2 [L : ℚ]`, `rootDiscr K ≤ 2 * rootDiscr L`, and such that every prime
  `q ≡ 1 (mod 4)` splitting completely in `L` splits completely in `K`.

-/

open NumberField

open scoped Classical nonZeroDivisors

namespace Work
namespace Tower

/-- Given a totally real number field `L`, there is a CM number field `K = L(i)` which is a
quadratic extension of `L` of controlled root discriminant, in which all primes `≡ 1` mod `4`
splitting completely in `L` split completely. -/
theorem exists_cm_adjoin
    (L : Type) [Field L] [NumberField L] (hL : NumberField.IsTotallyReal L) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K)
      (_ : IsScalarTower ℚ L K) (_ : NumberField.IsCMField K),
      Module.finrank L K = 2 ∧ Module.finrank ℚ K = 2 * Module.finrank ℚ L ∧
      NumberField.rootDiscr K ≤ 2 * NumberField.rootDiscr L ∧
      (∀ (q : ℕ), Nat.Prime q → q % 4 = 1 → Work.Defs.SplitsCompletely q L →
        Work.Defs.SplitsCompletely q K) := by
  haveI := hL
  refine ⟨CMAdjoin.cmAdjoin L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ?_, ?_, ?_⟩
  · exact CMAdjoin.finrank_cmAdjoin L
  · exact CMAdjoin.finrank_cmAdjoin_rat L
  · exact CMAdjoin.rootDiscr_cmAdjoin_le L
  · intro q hq h4 hLq
    exact CMAdjoin.splitsCompletely_cmAdjoin L q hq h4 hLq

end Tower
end Work
