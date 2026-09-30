import Mathlib
import ChallengeDeps
import Submission.Work.Homology.Basic
import Submission.Work.Homology.Corollaries

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Good pairs

The map of pairs `(X, A) ⟶ (X, U)` induced by the identity of `X` when `A ⊆ U`:
used to compare the long exact sequence of the pair `(X,A)` with that of `(X,U)`
when `A` is a deformation retract of `U` (so that the two relative homology groups
coincide, by the five lemma).
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.Homology

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

/-- The map of pairs `(X, A) ⟶ (X, U)` given by the identity of `X`, for
`A ⊆ U`. -/
def pairHomOfSubset {X : TopCat} {A U : Set X} (h : A ⊆ U) : PairHom X X A U where
  hom := 𝟙 X
  mapsTo := fun _ hx => h hx

@[simp]
theorem pairHomOfSubset_hom {X : TopCat} {A U : Set X} (h : A ⊆ U) :
    (pairHomOfSubset h).hom = 𝟙 X := rfl

end

end Work.DeltaHomology
