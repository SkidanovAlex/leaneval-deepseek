import Submission.Work.BoxShrink.PinchOff.PairingData
import Submission.Work.BoxShrink.PinchOff.windingSpan_union_le_sup_of_alternatingPartitionData_general

/-!
# The two-piece bound of the winding span

The pinch cuts the box region into two pieces `A`, `B` whose union is the box region and whose
intersection is the *interface* of the pinch (the slice `Σ` in the parent chapter's formulation, an
enlargement of it in `CollarPair.lean`).  Whenever

* the two pieces carry the **connector-free** alternating-partition datum
  (`AlternatingPartitionDataWeak`, produced from the crossing finiteness of the loops by the sign
  split, `SignSplit.lean`), and
* their intersection is **path connected** — so that the connectors of the datum exist inside it,

the winding span of the union is the supremum of the two spans
(`windingSpan_union_le_sup_of_weakData_of_isPathConnected_inter`), and hence vanishes as soon as
both pieces span nothing (`windingSpan_union_eq_bot_of_weakData_of_isPathConnected_inter`).

This is the only form of the two-piece bound the pinch consumes: it is
`windingSpan_union_le_sup_of_alternatingPartitionData_general` composed with the conversion of the
connector-free datum into the datum with connectors
(`AlternatingPartitionDataWeak.toData_of_isPathConnected_inter`), and it holds for **any** pair of
subsets of the carrier — no closedness, no openness, no smoothness.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The two-piece bound.**  Two sets of the carrier carrying the connector-free alternating
partition datum and meeting in a path connected set span at most the supremum of their spans. -/
theorem windingSpan_union_le_sup_of_weakData_of_isPathConnected_inter
    {P : Work.CoreTopology.ParamTorus} {A B : Set R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (hpart : AlternatingPartitionDataWeak P A B) (hconn : IsPathConnected (A ∩ B)) :
    Work.SurgeryInvariance.WindingSpan P (A ∪ B) ≤
      Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P B :=
  windingSpan_union_le_sup_of_alternatingPartitionData_general hAc hBc
    (hpart.toData_of_isPathConnected_inter hconn)

/-- **The vanishing form of the two-piece bound.**  If both pieces of a two-piece decomposition of
a region are inessential and meet in a path connected set, the region is inessential. -/
theorem windingSpan_union_eq_bot_of_weakData_of_isPathConnected_inter
    {P : Work.CoreTopology.ParamTorus} {A B : Set R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (hpart : AlternatingPartitionDataWeak P A B) (hconn : IsPathConnected (A ∩ B))
    (hA : Work.SurgeryInvariance.WindingSpan P A = ⊥)
    (hB : Work.SurgeryInvariance.WindingSpan P B = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (A ∪ B) = ⊥ := by
  have h := windingSpan_union_le_sup_of_weakData_of_isPathConnected_inter hAc hBc hpart hconn
  rw [hA, hB, sup_bot_eq] at h
  exact le_bot_iff.mp h

end

end Work.BoxShrink.PinchOff
