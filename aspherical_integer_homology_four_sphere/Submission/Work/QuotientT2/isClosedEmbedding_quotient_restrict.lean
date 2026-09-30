/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quotient map restricted to a closed set on which the relation is trivial

Let `X` be a compact Hausdorff space and `r` a setoid on `X` whose graph
`{(x, y) | r x y}` is closed.  If `s ⊆ X` is closed and `r` is trivial on `s`
(`r x y` with `x, y ∈ s` forces `x = y`), then the restricted quotient map
`fun x : s => Quotient.mk r x` is a closed embedding.

This is the geometric input for gluing a compact polytope along closed facets:
a facet on which the identification relation is injective sits inside the
quotient as a closed copy of itself.

The proof is the standard "compact to Hausdorff" argument: the domain `s` is
compact, the quotient `Quotient r` is Hausdorff (`t2_quotient_of_closed`), and a
continuous injective map from a compact space to a Hausdorff space is a closed
embedding.
-/
import Mathlib
import Submission.Work.QuotientT2.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.QuotientT2

theorem isClosedEmbedding_quotient_restrict {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (r : Setoid X) (hr : IsClosed {p : X × X | r p.1 p.2}) {s : Set X}
    (hs : IsClosed s) (hinj : ∀ x ∈ s, ∀ y ∈ s, r x y → x = y) :
    Topology.IsClosedEmbedding (fun x : s => Quotient.mk r (x : X)) := by
  -- The quotient is Hausdorff because the graph of `r` is closed.
  have hT2 : T2Space (Quotient r) := t2_quotient_of_closed hr
  -- The domain `s` is compact, being a closed subset of the compact space `X`.
  have hC : CompactSpace s := isCompact_iff_compactSpace.mp hs.isCompact
  -- The restricted quotient map is continuous, injective, and closed.
  have hcont : Continuous (fun x : s => Quotient.mk r (x : X)) :=
    (continuous_quotient_mk' (s := r)).comp continuous_subtype_val
  have hinj' : Function.Injective (fun x : s => Quotient.mk r (x : X)) := by
    intro a b hab
    exact Subtype.ext (hinj a.1 a.2 b.1 b.2 (Quotient.exact hab))
  have hclosed : IsClosedMap (fun x : s => Quotient.mk r (x : X)) :=
    Continuous.isClosedMap hcont
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont hinj' hclosed

end Work.QuotientT2
