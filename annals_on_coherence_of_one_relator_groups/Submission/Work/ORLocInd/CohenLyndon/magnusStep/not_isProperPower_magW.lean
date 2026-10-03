import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.magnusStepDefs

universe u

namespace Work.ORLocInd.CohenLyndon.magnusStep

/-- **The Magnus rewriting of a relator which is not a proper power is not a proper power.**

The base map `magBetaMap t r` of the Magnus decomposition expands the decorated letter `(x, k)` to
the conjugate `t ^ k * x * t ^ (-k)` of the original generators, and it sends the rewriting back to
the relator: `magBetaMap t r (magW t r) = r` when `σ_t r = 0` (`magBetaMap_magW`).  Since
`magBetaMap t r` is a homomorphism, a proper power decomposition `magW t r = u ^ m` descends to the
proper power decomposition `r = (magBetaMap t r u) ^ m` of `r` itself. -/
theorem not_isProperPower_magW {α : Type u} [DecidableEq α] (r : FreeGroup α) (t : α)
    (hpp : ¬ Work.OROneRel.IsProperPower r) (hσ : Work.OROneRel.eps t r = 0) :
    ¬ Work.OROneRel.IsProperPower (magW t r) := by
  rintro ⟨u, m, hm, hu⟩
  refine hpp ⟨magBetaMap t r u, m, hm, ?_⟩
  calc r = magBetaMap t r (magW t r) := (magBetaMap_magW t r hσ).symm
    _ = magBetaMap t r (u ^ m) := by rw [hu]
    _ = (magBetaMap t r u) ^ m := by rw [map_pow]

end Work.ORLocInd.CohenLyndon.magnusStep
