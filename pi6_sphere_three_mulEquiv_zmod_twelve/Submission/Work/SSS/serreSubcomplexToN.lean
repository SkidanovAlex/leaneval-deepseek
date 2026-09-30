import Mathlib
import Submission.Work.SSS.serreE1Defs
import Submission.Work.StemsB.SerreFiltration
import Submission.Work.SSS.serreSkelNodeg

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite in
theorem serreSubcomplexToN {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    (x : X _⦋n⦌) :
    x ∈ (Work.StemsB.serreSubcomplex f P).obj (op ⦋n⦌) ↔
      (SSet.S.mk (f.app (op ⦋n⦌) x)).toN.dim < P := by
  rw [Work.StemsB.mem_serreSubcomplex]
  exact Work.SSS.serreSkelNodeg (f.app (op ⦋n⦌) x)

end Work.SSS

