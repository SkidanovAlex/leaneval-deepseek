import Mathlib
import Submission.Work.DSCOH.Norm.Defs

namespace Work.DSCOH.Norm

universe w

theorem exists_adjacent_repeat {ι : Type w} [LinearOrder ι] {n : ℕ} {x : Fin (n + 2) → ι}
    (hx : Monotone x) (h : ¬ StrictMono x) :
    ∃ p : Fin (n + 1), x p.castSucc = x p.succ := by
  by_contra hc
  push Not at hc
  exact h (Fin.strictMono_iff_lt_succ.2 fun i =>
    lt_of_le_of_ne (hx (Fin.castSucc_le_succ i)) (hc i))

end Work.DSCOH.Norm
