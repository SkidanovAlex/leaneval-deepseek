import Mathlib
import Submission.Work.ORHughesFree.Section6.Reduce

namespace Work.Section6

theorem unitsTimesSubgroup_conj {K : Type} [Monoid K] {G : Type} [Group G]
    (N : Subgroup G) (hN : N.Normal) (t : G) (k : ℤ) (n : Kˣ × G)
    (hn : n ∈ Work.ORHughesFree.unitsTimesSubgroup (K := K) N) :
    ((n.1, t ^ k * n.2 * t ^ (-k)) : Kˣ × G) ∈
      Work.ORHughesFree.unitsTimesSubgroup (K := K) N := by
  rw [Work.ORHughesFree.mem_unitsTimesSubgroup] at hn ⊢
  simpa only [zpow_neg] using hN.conj_mem n.2 hn (t ^ k)

end Work.Section6
