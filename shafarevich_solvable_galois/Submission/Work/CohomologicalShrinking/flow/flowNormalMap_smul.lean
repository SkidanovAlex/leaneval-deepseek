/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `G`-equivariance of the rank-change map `flowNormalMap`

`flowNormalMap` is the map `F(m)/F(m)^{(i,j)} →* F(n)/F(n)^{(i,j)}` induced by a surjective
`G`-operator homomorphism `F(m) ⇢ F(n)` (`Work.CohomologicalShrinking.gradedMapMul`).  This file
records that it is `G`-equivariant for the action of `G` on the graded pieces of the refined
filtration.  The argument is the multiplicative form of
`Work.CohomologicalShrinking.functorial.gradedMapAdd_smul`, which is `gradedMapMul` transported
along the additive equivalence `Additive`.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Semidirect
import Submission.Work.CohomologicalShrinking.functorial.gradedMapAdd_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.flow

open Work.CohomologicalShrinking

theorem flowNormalMap_smul (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (g : G)
    (x : refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j) :
    flowNormalMap p G i j Φ (g • x) = g • flowNormalMap p G i j Φ x := by
  have h := functorial.gradedMapAdd_smul (p := p) (G := G)
      (P := Work.Shrinking.freeOperatorGroup G m)
      (Q := Work.Shrinking.freeOperatorGroup G n)
      Φ.toHom Φ.surjective Φ.equivariant i j g (Additive.ofMul x)
  change Additive.ofMul (flowNormalMap p G i j Φ (g • x)) =
      Additive.ofMul (g • flowNormalMap p G i j Φ x)
  exact h

end Work.CohomologicalShrinking.flow
