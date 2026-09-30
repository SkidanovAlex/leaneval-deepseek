/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Topology of the quotient presented by a class atlas

Consequences of `ClassAtlas.isClosed_relGraph` for the quotient: the quotient map is closed, and
a closed domain on which the relation is trivial embeds in the quotient as a closed subset (this
is how the truncation tori `T_v ⊆ M̄` of the Ratcliffe--Tschantz construction are recognised).
-/
import Mathlib
import Submission.Work.QuotientT2.ClassAtlas
import Submission.Work.QuotientT2.isClosedEmbedding_quotient_restrict

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Topology Function

namespace Work.QuotientT2

namespace ClassAtlas

variable {X : Type*} [TopologicalSpace X] (A : ClassAtlas X)

/-- The quotient map of a class atlas on a compact Hausdorff space is a closed map. -/
theorem isClosedMap_quotient_mk [CompactSpace X] [T2Space X] :
    IsClosedMap (Quotient.mk A.setoid) :=
  isClosedMap_quotient_mk_of_isClosed_relGraph A.isClosed_relGraph

/-- **A closed domain on which the relation is trivial embeds as a closed subset of the
quotient.** -/
theorem isClosedEmbedding_restrict [CompactSpace X] [T2Space X] {s : Set X} (hs : IsClosed s)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, A.rel x y → x = y) :
    Topology.IsClosedEmbedding (fun x : s => (Quotient.mk A.setoid (x : X) : Quotient A.setoid)) :=
  isClosedEmbedding_quotient_restrict A.setoid (by simpa [relGraph] using A.isClosed_relGraph)
    hs hinj

end ClassAtlas

end Work.QuotientT2
