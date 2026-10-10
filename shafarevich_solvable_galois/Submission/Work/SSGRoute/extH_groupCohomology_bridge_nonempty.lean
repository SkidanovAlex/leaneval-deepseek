import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.effStep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 3200000

/-!
# The `Ext`/group-cohomology bridge (node `E0b`), assembled

`Work.SSGRoute.Phi1.ExtGroupCohomologyBridge` (`Submission/Work/SSGRoute/phi1_defs.lean`)
packages the existence of a family of additive isomorphisms

`e n G A : Hⁿ(G,A) ≃+ Extⁿ_G(ℤ,A)`

which is natural in the coefficient module `A` at a fixed group and which is compatible, up to
sign, with the connecting maps of a short exact sequence of coefficient modules.

The construction is the Grothendieck/effacement induction:

* `Submission/Work/SSGRoute/effSES_defs.lean` chooses for every `A` an injective effacement
  `A ↪ I(A)` acyclic for both `H^•` and `Ext^•` in positive degrees, forms the effacement short
  exact sequence `effSES A = 0 → A → I(A) → coker → 0` with connecting maps `dH` (group side) and
  `dE` (`Ext` side), and defines the descent `eStep` of `dE ∘ e` along the surjection `dH`.
* `Submission/Work/SSGRoute/effStep.lean` proves that this descent is bijective, natural in the
  coefficients and compatible with connecting maps, so that it can be iterated.
* Here the iteration `eSeq` is run, starting from the canonical degree-`0` isomorphism `eZero`,
  and the resulting family is packaged as an `ExtGroupCohomologyBridge`.
-/

namespace Work.SSGRoute

open CategoryTheory

noncomputable section

/-- **The `Ext`/group-cohomology bridge** (node `E0b`): there is a family of additive
isomorphisms `Hⁿ(G,A) ≃+ Extⁿ_G(ℤ,A)` natural in the coefficient module `A` (at a fixed group)
and compatible, up to sign, with the connecting maps of short exact sequences. -/
theorem extH_groupCohomology_bridge_nonempty :
    Nonempty (Work.SSGRoute.Phi1.ExtGroupCohomologyBridge) :=
  ⟨{ e := fun n H _ A => eSeqFun H n A
     naturality := fun n H _ A B φ y => eSeqFun_nat H n A B φ y
     delta := fun n H _ S hS y => Or.inl (eSeqFun_delta H n S hS y) }⟩

end

end Work.SSGRoute
