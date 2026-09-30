import Mathlib
import Submission.Work.BMF.vke_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- `μ = (t/2π)(k-1)!/(N-1)^k > 0` for `2 ≤ N ≤ t`. -/
lemma vkMu_pos (N t : ℝ) (hN : 2 ≤ N) (hNt : N ≤ t) : 0 < vkMu N t := by
  have hN1 : 0 < N - 1 := by linarith
  have ht : 0 < t := by linarith
  have hfac : 0 < ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ) := by
    have : 0 < Nat.factorial (vkK N t - 1) := Nat.factorial_pos _
    exact_mod_cast this
  rw [vkMu]
  positivity

lemma vke_H_pos (N t : ℝ) (hN : 2 ≤ N) (hNt : N ≤ t) : 0 < vkH N t := by
  rw [vkH]
  exact Real.rpow_pos_of_pos (vkMu_pos N t hN hNt) _

end Work.BMF
