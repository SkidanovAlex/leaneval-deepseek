import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSHallW

/-- If `S` is a Sylow `p`-subgroup and `A ≤ S`, and `B` is a `p`-subgroup normalizing `A`,
then `A` and `B` are both contained in a common Sylow `p`-subgroup.

Indeed `A ⊔ B` is a `p`-subgroup (`IsPGroup.to_sup_of_normal_left'`, using `B ≤ N_G(A)`),
so some Sylow subgroup contains it (`IsPGroup.exists_le_sylow`); that Sylow contains both
`A` and `B`. -/
theorem exists_sylow_le_sup {G : Type*} [Group G] {p : ℕ}
    (S : Sylow p G) {A B : Subgroup G} (hA : A ≤ (S : Subgroup G)) (hB : IsPGroup p B)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    ∃ T : Sylow p G, A ≤ (T : Subgroup G) ∧ B ≤ (T : Subgroup G) := by
  have hApg : IsPGroup p A := S.isPGroup'.to_le hA
  have hsup : IsPGroup p (A ⊔ B : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hApg hB hBA
  obtain ⟨T, hT⟩ := IsPGroup.exists_le_sylow hsup
  exact ⟨T, le_trans le_sup_left hT, le_trans le_sup_right hT⟩

end Work.BSHallW
