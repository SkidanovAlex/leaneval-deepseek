import Mathlib
import Submission.Work.NPC.Frobenius.PResidual

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Frobenius

/-- The second isomorphism theorem in index form: if `M` is a normal subgroup of `G`, then the
index of `M ⊓ P` in `M` equals the index of `P` in the join `M ⊔ P`. -/
theorem relIndex_inf_eq_relIndex_sup_of_normal {G : Type*} [Group G] [Finite G]
    (M P : Subgroup G) [M.Normal] :
    (M ⊓ P).relIndex M = P.relIndex (M ⊔ P) := by
  have hA : (M ⊓ P).relIndex P * P.relIndex (M ⊔ P) = (M ⊓ P).relIndex (M ⊔ P) :=
    Subgroup.relIndex_mul_relIndex (M ⊓ P) P (M ⊔ P) inf_le_right le_sup_right
  have hB : (M ⊓ P).relIndex M * M.relIndex (M ⊔ P) = (M ⊓ P).relIndex (M ⊔ P) :=
    Subgroup.relIndex_mul_relIndex (M ⊓ P) M (M ⊔ P) inf_le_left le_sup_left
  have hE : (M ⊓ P).relIndex P = M.relIndex (M ⊔ P) := by
    rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_sup_left]
  have hz : 0 < M.relIndex (M ⊔ P) :=
    Nat.pos_of_ne_zero
      (@Subgroup.relIndex_ne_zero G _ M (M ⊔ P) (Subgroup.isFiniteRelIndex_of_finiteIndex))
  rw [hE] at hA
  refine Nat.mul_right_cancel hz ?_
  rw [hB, ← hA, mul_comm]

/-- If `P` is a Sylow `p`-subgroup of a finite group `G` and `M ⊴ G` is normal, then
`M ⊓ P`, viewed as a subgroup of `M`, is a Sylow `p`-subgroup of `M`. -/
theorem exists_sylow_subgroupOf_inf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {M : Subgroup G} [M.Normal] :
    ∃ S : Sylow p M, (S : Subgroup M) = (M ⊓ (P : Subgroup G)).subgroupOf M := by
  have hHp : IsPGroup p ((M ⊓ (P : Subgroup G)).subgroupOf M) :=
    P.isPGroup'.to_inf_right.comap_subtype
  have hkey := relIndex_inf_eq_relIndex_sup_of_normal M (P : Subgroup G)
  have hdvd : (M ⊓ (P : Subgroup G)).relIndex M ∣ (P : Subgroup G).index :=
    hkey ▸ Subgroup.relIndex_dvd_index_of_le
      (le_sup_right : (P : Subgroup G) ≤ M ⊔ (P : Subgroup G))
  have hidx : ¬ p ∣ ((M ⊓ (P : Subgroup G)).subgroupOf M).index :=
    fun h => Sylow.not_dvd_index P (h.trans hdvd)
  exact ⟨hHp.toSylow hidx, IsPGroup.toSylow_coe hHp hidx⟩

end Work.NPC.Frobenius
