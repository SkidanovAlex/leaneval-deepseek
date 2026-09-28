import Submission.Work.Rat.U.EMVanAll
import Submission.Work.Rat.U.EMVanOne
import Submission.Work.Rat.U.C3
import Submission.Work.Serre.serreE3a

/-!
# The C3 chain reconstructed from unblocked modules

`Work.Rat.U.C3` / `EMVanOne` / `EMVanAll` are copies of the SERRE chapter's `serreC3Finite`,
`serreRangeEMVanOneFin` and `serreRangeEMVanAllFin`, with the single blocked import (the lens-space
acyclicity's `isZero_ratH_sph_bottom`) replaced by an unblocked proof.  This module collects the
consequences used by the rational-homotopy-of-spheres computation.
-/

namespace Work.Rat

noncomputable section

/-- **`SerreC3Finite`, reconstructed** (the SERRE chapter's proof, with the blocked import of
`RatHurewicz/truncationHomologyTransfer_of_serre` replaced). -/
theorem serreC3Finite_reproved : Work.Serre.SerreC3Finite := Work.Serre.serreC3Finite

/-- **`RangeEMVanAllFin` from `SerreE3a`** (the finite-coefficient range form of C3, all degrees). -/
theorem rangeEMVanAllFin_reproved (hE3a : Work.Serre.SerreE3a) : Work.Serre.RangeEMVanAllFin :=
  Work.Serre.serreRangeEMVanAllFin hE3a
    (Work.Serre.serreRangeEMVanOneFin_noC0 Work.Serre.serreC3Finite)

end

end Work.Rat
