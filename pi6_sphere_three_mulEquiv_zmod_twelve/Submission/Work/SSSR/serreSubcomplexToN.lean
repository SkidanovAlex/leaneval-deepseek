import Mathlib
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.SSSR.StemsB.SerreFiltration
import Submission.Work.SSSR.serreSkelNodeg
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite in
theorem serreSubcomplexToN {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    (x : X _⦋n⦌) :
    x ∈ (Work.SSSR.StemsB.serreSubcomplex f P).obj (op ⦋n⦌) ↔
      (SSet.S.mk (f.app (op ⦋n⦌) x)).toN.dim < P := by
  rw [Work.SSSR.StemsB.mem_serreSubcomplex]
  exact Work.SSSR.serreSkelNodeg (f.app (op ⦋n⦌) x)

end Work.SSSR

