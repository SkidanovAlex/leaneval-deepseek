import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.removesOneCurve_of_cleanOneCurve

/-!
# `CleansDiscs` from `CleanOneCurve`

This file assembles the two-step chain that turns the *one* cut-and-paste of Pardon's second
innermost argument — stated in the geometric vocabulary of `SliceDisc` as
`Work.Topology.SphereSlicing.CleanOneCurve P` — into the full cleaning step
`Work.InnermostDisk.CleansDiscs P` consumed by the reduction of Pardon's Lemma 4.2:

1. `Work.Topology.SphereSlicing.removesOneCurve_of_cleanOneCurve` forgets the fields of an
   `InnermostDisc` that `SliceDisc` does not carry (the ambient set `S`, the containment of the
   curve and of the disc in `S`, and the essentiality of the boundary): an innermost disc *is* a
   slice disc, the cut-and-paste returns a slice disc with the same boundary and strictly fewer
   intersection curves, and that slice disc is re-read as an innermost disc at the ambient set
   `Set.range e'` (the replacement disc is its own ambient set).  This is
   `Work.InnermostDisk.RemovesOneCurve P`.
2. `Work.InnermostDisk.cleansDiscs_of_removesOneCurve` iterates that single step: the number of
   intersection curves strictly decreases along the sequence of replacements, so it reaches `0`,
   at which point the boundary curve already bounds a disc in the complement of `F`
   (`Work.InnermostDisk.boundsDiskInComplement_of_isEmpty`).

No geometric content is added here; the classical facts are localized in `CleanOneCurve P`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.SphereSlicing

noncomputable section

/-- **Pardon's second innermost argument: the single cut-and-paste, iterated.**

The single cut-and-paste `Work.Topology.SphereSlicing.CleanOneCurve P` implies the full cleaning
step `Work.InnermostDisk.CleansDiscs P`: every innermost disc whose interior meets `F` only in
inessential simple closed curves can be modified, keeping its boundary fixed, so that its
interior is disjoint from `F`.

The proof composes the structural passage to the consumed vocabulary
(`removesOneCurve_of_cleanOneCurve`) with the strictly-decreasing induction on the number of
intersection curves (`cleansDiscs_of_removesOneCurve`). -/
theorem cleansDiscs_of_cleanOneCurve {P : Work.CoreTopology.ParamTorus}
    (h : Work.Topology.SphereSlicing.CleanOneCurve P) :
    Work.InnermostDisk.CleansDiscs P :=
  Work.InnermostDisk.cleansDiscs_of_removesOneCurve (removesOneCurve_of_cleanOneCurve h)

end

end Work.Topology.SphereSlicing
