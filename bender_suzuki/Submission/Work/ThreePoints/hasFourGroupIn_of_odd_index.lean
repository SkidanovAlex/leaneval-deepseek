import Mathlib
import Submission.Work.Reductions.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

theorem hasFourGroupIn_of_odd_index {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    (hidx : Odd L.index) (hfour : Submission.Blueprint.HasFourGroup G) :
    Work.Reductions.HasFourGroupIn L := by
  -- Any involution of `G` lies in `L`: its image in `G ⧸ L` has order dividing both `2`
  -- and `L.index`, and `L.index` is odd, so that image is trivial.
  obtain ⟨a, b, ha, hb, hab, hcomm⟩ := hfour
  have hmem : ∀ x : G, orderOf x = 2 → x ∈ L := by
    intro x hx
    set d := orderOf ((QuotientGroup.mk' L) x) with hd
    have hdvd2 : d ∣ 2 := by
      rw [hd, ← hx]
      exact orderOf_map_dvd (QuotientGroup.mk' L) x
    have hodd : Odd d := by
      have hdvdidx : d ∣ L.index := by
        rw [hd, Subgroup.index_eq_card]
        exact orderOf_dvd_natCard _
      exact hidx.of_dvd_nat hdvdidx
    have hd1 : d = 1 := by
      have hcop : d.Coprime 2 := hodd.coprime_two_right
      exact Nat.dvd_one.mp (hcop.dvd_of_dvd_mul_left (by simpa using hdvd2))
    have hq : (QuotientGroup.mk' L) x = 1 := by
      rw [← orderOf_eq_one_iff]; exact hd1
    refine (QuotientGroup.eq_one_iff x).mp ?_
    rwa [QuotientGroup.mk'_apply] at hq
  exact ⟨a, b, hmem a ha, hmem b hb, ha, hb, hab, hcomm⟩

end Work.ThreePoints
