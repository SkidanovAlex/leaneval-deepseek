import Submission.Work.Stems.Hur2.ConeSurj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cone map of the square is a quotient map

`IC 1 × IC 1` is compact and `IC 2` is Hausdorff, so the continuous surjection `coneMap` is a closed
map, hence a quotient map.  This is what lets a null-homotopy of the boundary loop descend to a
filling square.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

instance : CompactSpace unitInterval := isCompact_iff_compactSpace.mp isCompact_Icc

instance : CompactSpace (IC 1) := inferInstance

instance : CompactSpace (IC 1 × IC 1) := inferInstance

theorem isClosedMap_coneMap : IsClosedMap (coneMap : IC 1 × IC 1 → IC 2) := fun s hs =>
  (hs.isCompact.image coneMap.continuous).isClosed

/-- **`coneMap` is a quotient map.** -/
theorem isQuotientMap_coneMap : Topology.IsQuotientMap (coneMap : IC 1 × IC 1 → IC 2) :=
  isClosedMap_coneMap.isQuotientMap coneMap.continuous coneMap_surjective

end

end Work.Stems.Hur2
