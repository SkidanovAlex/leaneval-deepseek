import Mathlib
import Submission.Work.BMF.recursion.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- Splitting a sum over `Fin S` into the first `k` coordinates and the remaining `S - k`
coordinates. -/
theorem sum_split_fin {M : Type*} [AddCommMonoid M] {k S : ℕ} (hkS : k ≤ S) (f : Fin S → M) :
    ∑ i : Fin S, f i = ∑ i : Fin k, f (hIdx hkS i) + ∑ r : Fin (S - k), f (tIdx hkS r) := by
  rw [← Equiv.sum_comp (finCongr (Nat.add_sub_of_le hkS)) f]
  rw [Fin.sum_univ_add (fun i : Fin (k + (S - k)) => f (finCongr (Nat.add_sub_of_le hkS) i))]
  congr 1

end Work.BMF.recursion
