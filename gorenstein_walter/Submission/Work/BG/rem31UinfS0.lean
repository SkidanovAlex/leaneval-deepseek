import Mathlib
import Submission.Work.BG.nCases
import Submission.Work.BG.hyp12OfBGData

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 in
theorem rem31UinfS0 {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    D.U ⊓ D.S0 = ⊥ := by
  -- `U = O(H)` is a `2'`-group: it is an `opiCoreInG` for the set of odd primes.
  have hUpi : Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) D.U := by
    change Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) (Work.GW2.oddCoreIn D.H)
    rw [Work.GW2.oddCoreIn_eq_opiCoreInG]
    exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _
  -- the Sylow `2`-subgroup `S` is a `π`-group for `π = {2}`, so `U ⊓ S = ⊥`
  have hUinfS : D.U ⊓ (D.S : Subgroup G) = ⊥ :=
    OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl hUpi
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem D.S.isPGroup' (by simp))
  -- and `S₀ ≤ S`, so `U ⊓ S₀ ≤ U ⊓ S = ⊥`
  have hle : D.U ⊓ D.S0 ≤ D.U ⊓ (D.S : Subgroup G) := inf_le_inf_left _ D.S0_le
  rw [hUinfS] at hle
  exact le_bot_iff.mp hle

end Work.BG
