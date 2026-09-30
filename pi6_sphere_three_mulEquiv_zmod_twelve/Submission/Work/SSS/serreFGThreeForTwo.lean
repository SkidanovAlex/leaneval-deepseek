import Mathlib
import Submission.Work.SSS.Assembly
import Submission.Work.SSS.packetOfFiltration
import Submission.Work.SSS.serreE2

/-!
# Serre's three-for-two theorem (`Work.PiS.SerreFGThreeForTwo`)

The final assembly.  `Work.SSS.serreFG_of_pieces` (file `Assembly.lean`, sorry-free) derives
`Work.PiS.SerreFGThreeForTwo` from the two inputs

* `Work.SSS.PacketStatement` — the convergence theorem for the spectral sequence of a saturated
  filtration (`SSPacket`), proved as `Work.SSS.packetOfFiltration`
  (`Submission/Work/SSS/packetOfFiltration.lean`), and
* `Work.SSS.SerreE2Statement` — the E² page of the Serre filtration of the singular chains of `p`
  (`E²_{s,t} ≅ H_s(B; H_t F)`, read in the Serre class of finitely generated abelian groups),
  proved as `Work.SSS.serreE2` (`Submission/Work/SSS/serreE2.lean`) from the first page theorem
  `Work.SSS.serreE1` (`Submission/Work/SSS/serreE1.lean`) and the passage to the Serre class
  `Work.SSS.serreE2OfE1` (`Submission/Work/SSS/serreE2OfE1.lean`).
-/

set_option autoImplicit false

namespace Work.SSS

noncomputable section

theorem serreFGThreeForTwo : Work.PiS.SerreFGThreeForTwo :=
  serreFG_of_pieces (fun C ξ => packetOfFiltration C ξ) serreE2

end

end Work.SSS
