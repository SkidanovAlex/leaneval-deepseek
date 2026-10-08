import Mathlib

namespace Work.AUTA7.GroupTheory

/-- The "other direction" of the second isomorphism theorem for relative indices:
if `N` is normal, then `H` has the same relative index in `H ⊔ N` as in `N`
(provided `N.relIndex H` is finite, so that cancellation is legitimate). -/
private theorem relIndex_sup_eq_relIndex_of_normal {G : Type*} [Group G] {H N : Subgroup G}
    (hN : N.Normal) (h : N.relIndex H ≠ 0) :
    H.relIndex (H ⊔ N) = H.relIndex N := by
  have hN' : N.Normal := hN
  have h1 : (H ⊓ N).relIndex H * H.relIndex (H ⊔ N) = (H ⊓ N).relIndex (H ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (H ⊓ N) H (H ⊔ N) inf_le_left le_sup_left
  have h2 : (H ⊓ N).relIndex N * N.relIndex (H ⊔ N) = (H ⊓ N).relIndex (H ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (H ⊓ N) N (H ⊔ N) inf_le_right le_sup_right
  rw [Subgroup.inf_relIndex_left H N] at h1
  rw [Subgroup.inf_relIndex_right H N] at h2
  have hNsup : N.relIndex (H ⊔ N) = N.relIndex H := Subgroup.relIndex_sup_right H N
  rw [hNsup] at h2
  have key : N.relIndex H * H.relIndex (H ⊔ N) = N.relIndex H * H.relIndex N :=
    h1.trans (h2.symm.trans (mul_comm _ _))
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero h) key

theorem SylowInfNormal {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime] (P : Sylow p Q)
    (L : Subgroup Q) (hL : L.Normal) :
    IsPGroup p ↥((P : Subgroup Q) ⊓ L) ∧ ¬ p ∣ ((P : Subgroup Q) ⊓ L).relIndex L := by
  constructor
  · exact IsPGroup.to_le P.isPGroup' inf_le_left
  · have hinst : (L.subgroupOf (P : Subgroup Q)).FiniteIndex := inferInstance
    have hfin : L.relIndex (P : Subgroup Q) ≠ 0 := hinst.index_ne_zero
    have hA : (P : Subgroup Q).relIndex ((P : Subgroup Q) ⊔ L) = (P : Subgroup Q).relIndex L :=
      relIndex_sup_eq_relIndex_of_normal hL hfin
    rw [Subgroup.inf_relIndex_right (P : Subgroup Q) L, ← hA]
    intro hdvd
    exact P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))

end Work.AUTA7.GroupTheory
