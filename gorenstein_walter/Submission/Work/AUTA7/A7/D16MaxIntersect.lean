import Mathlib
import Submission.Work.AUTA7.Defs

namespace Work.AUTA7.A7

/- Hint: the subgroups of order `8` of `DihedralGroup 8` are exactly the three index-2 subgroups
`⟨r 1⟩ ≅ C₈`, `⟨r 2, sr 0⟩` and `⟨r 2, sr 1⟩` (classify: `T ⊓ ⟨r 1⟩` has index `≤ 2` in `T`, and if
`T ≰ ⟨r 1⟩` then `T = ⟨r 2⟩ ⋊ ⟨sr i⟩`); all pairwise intersections are `⟨r 2⟩ ≅ C₄`, cyclic. Use
`DihedralGroup.r_mul_r`, `DihedralGroup.sr_mul_r`, `DihedralGroup.r_mul_sr`, `DihedralGroup.sr_mul_sr`,
`DihedralGroup.r_one_pow`, `DihedralGroup.orderOf_sr`. -/
/-- Every subgroup of index `2` of a group contains the square of every element
(`Subgroup.sq_mem_of_index_two`).  In `DihedralGroup 8` the squares generate `⟨r 2⟩ ≅ C₄`, so every
subgroup of order `8` contains `⟨r 2⟩`.  Since two distinct subgroups of order `8` have intersection
of cardinality `4`, the intersection is exactly `⟨r 2⟩`, hence cyclic.

We use the index of `T₁ ⊓ T₂` in `T₁` to bound the cardinality: the relative index is at least `2`
(the subgroup is proper, because otherwise `T₁ ≤ T₂` and equal cardinalities force `T₁ = T₂`) and
`Nat.card (T₁ ⊓ T₂) * relIndex * 2 = 16`. -/
theorem D16MaxIntersect : Work.GW2.D16MaxIntersectProp := by
  intro T₁ T₂ h1 h2 hne
  have hcardG : Nat.card (DihedralGroup 8) = 16 := by rw [DihedralGroup.nat_card]
  -- subgroups of order `8` have index `2` in the group of order `16`
  have hidx : ∀ T : Subgroup (DihedralGroup 8), Nat.card T = 8 → T.index = 2 := by
    intro T hT
    have h := Subgroup.card_mul_index T
    rw [hT, hcardG] at h
    omega
  -- hence they contain the squares, in particular `r 2 = (r 1) ^ 2`
  have hr2 : ∀ T : Subgroup (DihedralGroup 8), Nat.card T = 8 →
      (DihedralGroup.r 2 : DihedralGroup 8) ∈ T := by
    intro T hT
    have h := Subgroup.sq_mem_of_index_two (hidx T hT) (DihedralGroup.r 1 : DihedralGroup 8)
    simpa [DihedralGroup.r_one_pow] using h
  set K : Subgroup (DihedralGroup 8) := T₁ ⊓ T₂ with hK
  have hK1 : K ≤ T₁ := by rw [hK]; exact inf_le_left
  have hK2 : K ≤ T₂ := by rw [hK]; exact inf_le_right
  have hzple : Subgroup.zpowers (DihedralGroup.r 2 : DihedralGroup 8) ≤ K :=
    Subgroup.zpowers_le.mpr (by rw [hK]; exact Subgroup.mem_inf.mpr ⟨hr2 T₁ h1, hr2 T₂ h2⟩)
  -- `⟨r 2⟩` has order `4`, so `4 ≤ |T₁ ⊓ T₂|`
  have hzpcard : Nat.card (Subgroup.zpowers (DihedralGroup.r 2 : DihedralGroup 8)) = 4 := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r]
    decide
  have h4le : 4 ≤ Nat.card K := by
    rw [← hzpcard]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hzple)
      (Subgroup.inclusion_injective hzple)
  -- `T₁ ⊓ T₂` is a proper subgroup of `T₁`, since otherwise `T₁ = T₂`
  have hnotle : ¬ T₁ ≤ K := by
    intro hle
    have hle2 : T₁ ≤ T₂ := hle.trans hK2
    exact hne (Subgroup.eq_of_le_of_card_ge hle2 (by rw [h1, h2]))
  have hrel2 : 2 ≤ K.relIndex T₁ := by
    have hne_top : K.subgroupOf T₁ ≠ ⊤ := by
      intro h
      exact hnotle (Subgroup.subgroupOf_eq_top.mp h)
    have h := Subgroup.one_lt_index_of_ne_top hne_top
    show 2 ≤ (K.subgroupOf T₁).index
    omega
  -- Lagrange in `G`, combined with `[T₁ : K] ≥ 2`, gives `|K| ≤ 4`
  have hcard_eq : Nat.card K * (K.relIndex T₁ * 2) = 16 := by
    have h := Subgroup.card_mul_index K
    rw [hcardG] at h
    have hrel := Subgroup.relIndex_mul_index (H := K) (K := T₁) hK1
    rw [hidx T₁ h1] at hrel
    rw [← hrel] at h
    exact h
  have hle4 : Nat.card K ≤ 4 := by
    have hmono : Nat.card K * 4 ≤ Nat.card K * (K.relIndex T₁ * 2) := by
      apply Nat.mul_le_mul_left
      omega
    omega
  have hcardK : Nat.card K = 4 := le_antisymm hle4 h4le
  -- so `T₁ ⊓ T₂ = ⟨r 2⟩` is cyclic
  have heq : K = Subgroup.zpowers (DihedralGroup.r 2 : DihedralGroup 8) := by
    refine (Subgroup.eq_of_le_of_card_ge hzple ?_).symm
    rw [hcardK, hzpcard]
  rw [heq]
  infer_instance

end Work.AUTA7.A7
