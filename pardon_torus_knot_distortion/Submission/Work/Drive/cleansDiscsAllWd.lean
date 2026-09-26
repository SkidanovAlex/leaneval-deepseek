import Mathlib
import Submission.Work.Drive.InterfacesD
import Submission.Work.Drive.innermostDiscWindingDichotomy_of_disjoint

/-! Guidance from the project lead (the requester):

# Guidance (project lead) — cleansDiscsAllWd (field 1, CORRECTED)

The previous owner proved most of the machinery but found CleansDiscsAllW FALSE: InnermostDisc
allowed interior curves TOUCHING the boundary curve α (the lens/crescent example).  The corrected
statement adds the hypothesis that every interior curve is DISJOINT from α.  So all trace preimages
lie in the OPEN disc: by compactness, at positive distance from ∂𝔻.

This file assembles the target `Work.Drive.CleansDiscsAllWd` from the cut-and-paste machinery of
`Submission/Work/Drive/innermostDiscWindingDichotomy_of_disjoint.lean`, which contains exactly the
required ingredient:

* `Work.Drive.WeakDatum.ofInnermostDisc` turns an innermost-disc datum into a weak datum whose
  traces are the preimages of the intersection curves;
* the disjointness hypothesis (`∀ i, Disjoint (curves i) α`) says exactly that every trace lies
  strictly inside the model disc (`Work.Drive.kappa_strict_of_disjoint`); in that case there is no
  lens/crescent degeneracy, the outward tube of the innermost trace is a genuine annulus, its level
  `levP ∘ e - 1` has a single sign, and the single-sign surgery applies;
* `Work.Drive.boundsDiskInComplementW_of_innermostDisc_of_disjoint` is then the strong induction on
  the number of traces, producing the weak bounding disc.
-/

namespace Work.Drive

/-- The corrected weak cut-and-paste input (interior curves disjoint from the boundary curve). -/
theorem cleansDiscsAllWd : Work.Drive.CleansDiscsAllWd := by
  intro ψ S D hdisj
  exact boundsDiskInComplementW_of_innermostDisc_of_disjoint (ψ := ψ.toHomeomorph) D hdisj

end Work.Drive
