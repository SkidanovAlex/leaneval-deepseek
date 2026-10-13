import Mathlib
import Submission.Work.DSM1p.Family

namespace Work.DSM1p.Family

theorem of_f (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) {m n : ℕ} (h : m ≤ n)
    (y : Work.DSM1p.FamTower R p x m) :
    Work.DSM1p.FamClosure.of R p x n (Work.DSM1p.FamTower.stepMap R p x m n h y) =
      Work.DSM1p.FamClosure.of R p x m y := by
  exact Ring.DirectLimit.of_f h y

end Work.DSM1p.Family
