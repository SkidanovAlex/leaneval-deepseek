import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.Discriminant
import Submission.Work.Tower.Unramified.TotallyReal
import Submission.Work.Tower.Unramified.Compositum
import Submission.Work.Tower.Unramified.maxElemAbUnram3_isUnramified
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_descent
import Submission.Work.Tower.Unramified.finrank_maxElemAbUnram3_eq_pow_three
import Submission.Work.Tower.Unramified.splitsCompletely_iff_relative
import Submission.Work.Tower.Unramified.splitsCompletelyIn_maxElemAbUnram3_iff
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_sup
import Submission.Work.Tower.Unramified.MaxElemAb
import Submission.Work.Tower.Unramified.isUnramifiedExtensionForallPrimes_sup
import Submission.Work.Tower.Unramified.rootDiscr_le_of_algebra
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_ncard

/-!
# The unramified-extension and complete-splitting infrastructure (area `Tower/Unramified`)

Aggregator for the area.  Import this module to get all of it.

## Contents

* `Submission.Work.Tower.Unramified.Basic`: the predicate `IsUnramifiedExtensionForallPrimes`,
  its equivalence with the given `IsUnramifiedExtension` (Galois case), equivalent formulations
  via `Algebra.IsUnramifiedIn`/`Algebra.IsUnramifiedAt`, and the tower property.
* `Submission.Work.Tower.Unramified.Discriminant`: the relative different of an unramified
  extension is trivial, `|discr L| = |discr F| ^ [L:F]`, `rootDiscr L = rootDiscr F`,
  `1 ≤ rootDiscr K`.
* `Submission.Work.Tower.Unramified.TotallyReal`: total realness is preserved by unramified
  Galois extensions with `3`-group Galois group.
* `Submission.Work.Tower.Unramified.MaxElemAb`: `maxElemAbUnram3 F`, the maximal elementary
  abelian unramified `3`-extension, with its defining universal property.
* `Submission.Work.Tower.Unramified.isUnramifiedExtensionForallPrimes_sup`: the compositum of
  unramified extensions is unramified.
* `Submission.Work.Tower.Unramified.rootDiscr_le_of_algebra`: monotonicity of `rootDiscr`.
* `Submission.Work.Tower.Unramified.SplitsCompletelyIn_ncard`: the number of primes over `𝔭`.
* `Submission.Work.Tower.Unramified.SplitsCompletelyIn_descent`: complete splitting descends.
* `Submission.Work.Tower.Unramified.splitsCompletely_iff_relative`: the rational/relative bridge.

The lemmas living in the sub-namespace `Work.Tower.Unramified` are re-exported below under
`Work.Tower` so that callers can use a single namespace.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower

export Unramified (isUnramifiedExtensionForallPrimes_sup
  isUnramifiedExtensionForallPrimes_iff_formallyUnramified
  rootDiscr_le_of_algebra SplitsCompletelyIn_ncard maxElemAbUnram3_isUnramified
  maxElemAbUnram3_isElementaryAbelianThreeExtension
  isElementaryAbelianThreeExtension_sup
  exists_mem_unramifiedElemAbThreeSet_eq_maxElemAbUnram3 SplitsCompletelyIn_descent
  finrank_maxElemAbUnram3_eq_pow_three splitsCompletely_iff_relative
  splitsCompletelyIn_maxElemAbUnram3_iff SplitsCompletelyIn_sup)

end Tower
end Work
