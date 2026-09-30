import Mathlib
import Submission.Work.BMF.mr_direct.buchstab_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open Work.BMF.mrDirect

theorem card_filter_winPrimes_le_two (K : ℝ) (hK : 0 < K) (J : Finset ℕ) (p : ℕ) :
    (J.filter (fun j => p ∈ Work.BMF.mrDirect.winPrimes K j)).card ≤ 2 := by
  by_cases hp : p.Prime
  · -- a prime occurs only in the two windows with indices `jdex K p - 1`, `jdex K p`
    refine le_trans (Finset.card_le_card ?_) (card_winPrimes_le_two hK hp)
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨?_, hj.2⟩
    have hb := win_idx_bounds hK hj.2
    have hfl2 : K * Real.log (p : ℝ) < (jdex K p : ℝ) + 1 := by
      simp only [jdex]
      exact Nat.lt_floor_add_one _
    rw [Finset.mem_range]
    have : (j : ℝ) < (jdex K p : ℝ) + 1 := lt_of_le_of_lt hb.2 hfl2
    exact_mod_cast this
  · -- a non-prime lies in no window
    have hemp : J.filter (fun j => p ∈ Work.BMF.mrDirect.winPrimes K j) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro j _
      rw [mem_winPrimes]
      exact fun h => hp h.1
    rw [hemp]
    simp

end Work.BMF.mr_direct
