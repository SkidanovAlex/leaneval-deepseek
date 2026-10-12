import Mathlib.Data.Fintype.Prod
import Submission.Work.BoseBoxFock.cIPn_sum_aPC_re
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- `Submission.BoseGases.pairSet N` is the off-diagonal of `Finset.univ : Finset (Fin N)`:
the set of ordered pairs `(i,j)` with `i ≠ j`. -/
lemma pairSet_eq_univ_offDiag (N : ℕ) :
    Submission.BoseGases.pairSet N = (Finset.univ : Finset (Fin N)).offDiag := by
  ext p
  simp [Submission.BoseGases.pairSet, Finset.mem_offDiag]

theorem pairSet_card (N : ℕ) : (Submission.BoseGases.pairSet N).card = N * (N - 1) := by
  rw [pairSet_eq_univ_offDiag, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  exact (Nat.mul_sub_one N N).symm

end Work.BoseBoxFock
