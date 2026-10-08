import Mathlib
import Submission.Work.DoubleTransitivity.App2.SylowAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

theorem not_dvd_index_sylowIn_normalizer {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P W : Subgroup G} (hP : IsPGroup p P) (hPW : P ≤ W)
    (h : ¬ p ∣ P.relIndex (Subgroup.normalizer (P : Set G) ⊓ W)) :
    ¬ p ∣ (P.subgroupOf W).index := by
  -- View `P` as a subgroup of `W`; it is again a `p`-subgroup.
  have hQ : IsPGroup p (P.subgroupOf W) := hP.comap_subtype
  -- The normalizer of `P.subgroupOf W` inside `W` is `N_G(P) ⊓ W`.
  have hnorm : Subgroup.normalizer (P.subgroupOf W : Set W) =
      (Subgroup.normalizer (P : Set G) ⊓ W).subgroupOf W := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPW, Subgroup.inf_subgroupOf_right]
  -- Relative indices agree between the two descriptions.
  have hrel : (P.subgroupOf W).relIndex (Subgroup.normalizer (P.subgroupOf W : Set W)) =
      P.relIndex (Subgroup.normalizer (P : Set G) ⊓ W) := by
    rw [hnorm]
    exact Subgroup.relIndex_subgroupOf inf_le_right
  have hN : ¬ p ∣ (P.subgroupOf W).relIndex (Subgroup.normalizer (P.subgroupOf W : Set W)) := by
    rw [hrel]; exact h
  -- Apply the general Sylow-in-normalizer transfer inside `W`.
  exact Work.DoubleTransitivity.App2.not_dvd_index_of_not_dvd_relIndex_normalizer hQ hN

end Work.NormalComplement
