import Mathlib

namespace Work.CORE4.A4aAux

theorem sup_isMulCommutative {G : Type} [Group G] (H K : Subgroup G)
    (h : H ≤ Subgroup.centralizer (K : Set G))
    (hH : IsMulCommutative ↥H) (hK : IsMulCommutative ↥K) :
    IsMulCommutative ↥(H ⊔ K) := by
  rw [Subgroup.sup_eq_closure]
  apply Subgroup.isMulCommutative_closure
  rw [Set.pairwise_union]
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb _
    exact setLike_mul_comm (s := H) ha hb
  · intro a ha b hb _
    exact setLike_mul_comm (s := K) ha hb
  · intro a ha b hb _
    exact ⟨(Subgroup.mem_centralizer_iff.mp (h ha) b hb).symm,
           Subgroup.mem_centralizer_iff.mp (h ha) b hb⟩

end Work.CORE4.A4aAux
