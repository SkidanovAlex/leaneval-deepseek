import Mathlib
import ChallengeDeps
import Submission.Work.HomologyExtra.Basic
import Submission.Work.HomologyExtra.SimplexClass
import Submission.Work.HomologyExtra.GeneratorReduction
import Submission.Work.HomologyExtra.simplexBoundary_homology
import Submission.Work.HomologyExtra.relHomology_simplexPair

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The relative homology of the standard simplex pair

The computation `H_k(Δⁿ, ∂Δⁿ; ℤ) ≅ ℤ` for `k = n` and `0` otherwise, in the two forms used by the
rest of the project:

* `Work.HomologyExtra.relHomology_simplexPair` (delegated, see
  `Submission/Work/HomologyExtra/relHomology_simplexPair.lean`) — the isomorphism statement;
* `relHomology_simplexPair_iso` — the same, phrased with an explicit isomorphism;
* `relHomology_simplexPair_top` — the degree-`n` case, i.e. the input `Hₙ(Δⁿ,∂Δⁿ) ≅ ℤ` of
  `isIso_simplexGenMap_of_epi`.

The companion statement for the boundary sphere is
`Work.HomologyExtra.simplexBoundary_homology` (`H_k(∂Δⁿ⁺¹) ≅ ℤ` for `k = 0, n`, `0` otherwise).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- **The relative homology of the standard simplex pair**: `H_k(Δⁿ, ∂Δⁿ; ℤ)` is `ℤ` in degree `n`
and `0` otherwise (`n ≥ 1`). -/
theorem relHomology_simplexPair_iso (n k : ℕ) (hn : 1 ≤ n) :
    Nonempty (Work.Homology.relHomology Work.Homology.ZMod k (simplex n) (simplexBoundary n) ≅
      (if k = n then Work.Homology.ZMod else ModuleCat.of ℤ PUnit)) :=
  relHomology_simplexPair n k hn

/-- The top relative homology of the simplex pair is `ℤ`. -/
theorem relHomology_simplexPair_top (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (Work.Homology.relHomology Work.Homology.ZMod n (simplex n)
      (simplexBoundary n) ≅ Work.Homology.ZMod) := by
  have h := relHomology_simplexPair_iso n n hn
  simpa using h

end

end Work.HomologyExtra
