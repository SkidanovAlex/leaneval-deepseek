import Mathlib
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.iotaF_chainMap
import Submission.Work.SSSR.ezGen_snd_sum_zero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
noncomputable section

/-- The predecessor in the chain-complex shape `… → 2 → 1 → 0`. -/
lemma down_next_eq (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  rcases n with _ | k
  · rw [ComplexShape.next_eq_self' _ 0 (fun k hk => Nat.succ_ne_zero k hk)]
  · rw [ComplexShape.next_eq' _ (ComplexShape.down_mk (k + 1) k rfl)]
    omega

end

end Work.SSSR
