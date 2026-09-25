import Mathlib
import Submission.Work.CFTLib.ShafDeps
import Submission.Work.CFT.MaxProP.ContCohomology.Defs
import Submission.Work.CFTLib.ContCohomology.Setup
import Submission.Work.CFTLib.ContCohomology.Inhomogeneous
import Submission.Work.CFTLib.ContCohomology.P1Iso
import Submission.Work.CFTLib.ContCohomology.evalIter_mem_homCochain
import Submission.Work.CFTLib.ContCohomology.exists_evalIter_eq
import Submission.Work.CFTLib.ContCohomology.exists_homCochain_iso_iCochain
import Submission.Work.CFTLib.ContCohomology.continuousCohomology_iso_homShortComplex
import Submission.Work.CFTLib.ContCohomology.homShortComplex_homology_iso_iComplex
import Submission.Work.CFTLib.ContCohomology.iComplex_homology_two_iso_H2FpCont

namespace Work.CFTLib.ContCohomology

open TopRep

/-- **Continuous `H²` of a profinite group with trivial `𝔽_p`-coefficients is the filtered colimit
of the `H²` of its finite quotients.**

`Work.CFT.MaxProP.H2FpCont p G` is the filtered colimit of the abstract group cohomology groups
`H²(G ⧸ U, 𝔽_p)` over the open normal subgroups `U ◁ G`, along the inflation maps
(`Submission/Work/CFT/MaxProP/ContCohomology/Defs.lean`).  On the other hand
`continuousCohomology 2 (trivialZModpRep p G)` is Mathlib's continuous cohomology of the trivial
topological representation of `G` on the discrete module `𝔽_p`
(`Mathlib.RepresentationTheory.Homological.ContCohomology`), defined as the second homology of the
complex of invariants of the `coind₁`-resolution.

For a profinite (= compact, Hausdorff, totally disconnected, topological) group `G` the two agree:
a continuous equivariant cochain on `G^{n+1}` with values in the *discrete* module `𝔽_p` factors
through a finite quotient, and conversely every finite quotient contributes cocycles. -/
theorem two_iso_H2FpCont
    (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    Nonempty (continuousCohomology 2 (LeanEval.NumberTheory.trivialZModpRep p G) ≃ₗ[ZMod p]
      Work.CFT.MaxProP.H2FpCont p G) := by
  haveI : LocallyCompactSpace G := inferInstance
  -- The invariants of the `coind₁`-resolution form the homogeneous cochain complex.
  obtain ⟨e₁⟩ := continuousCohomology_iso_homShortComplex (X := trivRep p G) 1
  -- The homogeneous and inhomogeneous descriptions agree.
  obtain ⟨e₂⟩ := homShortComplex_homology_iso_iComplex (p := p) (Γ := G)
  -- The inhomogeneous complex computes the filtered colimit of the finite quotients.
  obtain ⟨e₃⟩ := iComplex_homology_two_iso_H2FpCont p (Γ := G)
  exact ⟨(e₁.trans e₂.toLinearEquiv).trans e₃⟩

end Work.CFTLib.ContCohomology
