import Mathlib
import Submission.Work.CORE3.CommutingInvolsCardSix

namespace Work.CORE3

/-- A group of order `6` cannot contain two distinct commuting involutions: the subgroup they
generate would be a Klein four group of order `4`, but `4 ∤ 6` (Lagrange).

This is the exact content of `Work.CORE3.CommutingInvolsCardSix`: in a group of order `6`, a
nontrivial involution `u` and a commuting involution `v` force `v = 1` or `v = u`, both of which
are excluded by the hypotheses. -/
theorem NoKleinFourOfCardSix {H : Type} [Group H] [Finite H] (hcard : Nat.card H = 6)
    {u v : H} (hu : u * u = 1) (hv : v * v = 1) (hcomm : u * v = v * u)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) : False := by
  have hu2 : u ^ 2 = 1 := by rw [pow_two]; exact hu
  have hv2 : v ^ 2 = 1 := by rw [pow_two]; exact hv
  rcases CommutingInvolsCardSix hcard u v hu2 hu1 hv2 hcomm with h | h
  · exact hv1 h
  · exact huv h.symm

end Work.CORE3
