import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- If `D = V ⊔ K`, `D` normalizes `K`, and `V` normalizes `A`, then `D` normalizes
`K ⊔ A`.  Indeed `K ≤ K ⊔ A ≤ normalizer (K ⊔ A)`, while `V` normalizes both `K`
(since `V ≤ D ≤ N(K)`) and `A` (by hypothesis), hence normalizes their join. -/
theorem sec4_c_normalizes {G : Type*} [Group G] {D V A K : Subgroup G}
    (hKD : D ≤ Subgroup.normalizer (K : Set G)) (hDV : D = V ⊔ K)
    (hVle : V ≤ D) (hAV : V ≤ Subgroup.normalizer (A : Set G)) :
    D ≤ Subgroup.normalizer ((K ⊔ A : Subgroup G) : Set G) := by
  rw [hDV]
  refine sup_le ?_ ?_
  · rw [Subgroup.le_normalizer_iff]
    intro v hv k hk
    have hvK : v ∈ Subgroup.normalizer (K : Set G) := le_trans hVle hKD hv
    have hvA : v ∈ Subgroup.normalizer (A : Set G) := hAV hv
    -- `v` conjugates `K` into `K ⊔ A` and `A` into `K ⊔ A`, hence `K ⊔ A` into `K ⊔ A`.
    have hK : K ≤ Subgroup.comap (MulAut.conj v : G →* G) (K ⊔ A) := by
      intro k hk
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hvK k).mp hk)
    have hA : A ≤ Subgroup.comap (MulAut.conj v : G →* G) (K ⊔ A) := by
      intro a ha
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hvA a).mp ha)
    exact Subgroup.mem_comap.mp (sup_le hK hA hk)
  · exact le_trans le_sup_left Subgroup.le_normalizer

end Work.NormalComplement
