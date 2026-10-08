import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Coprime.SZUtil

/-- If `G ⧸ N` is solvable, then so is `(G ⧸ A) ⧸ (N.map (mk' A))`: the natural map
`G → (G ⧸ A) ⧸ (N.map (mk' A))` kills `N`, hence factors through `G ⧸ N`, over which it is
surjective. -/
theorem isSolvable_quotient_map_mk {G : Type*} [Group G] {N A : Subgroup G} [N.Normal] [A.Normal]
    (hsol : Group.IsSolvable (G ⧸ N)) :
    Group.IsSolvable ((G ⧸ A) ⧸ (N.map (QuotientGroup.mk' A))) := by
  let φ : G →* (G ⧸ A) ⧸ (N.map (QuotientGroup.mk' A)) :=
    (QuotientGroup.mk' (N.map (QuotientGroup.mk' A))).comp (QuotientGroup.mk' A)
  have hker : N ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (N.map (QuotientGroup.mk' A)) (QuotientGroup.mk' A n) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_map_of_mem _ hn
  have hsurj : Function.Surjective (QuotientGroup.lift N φ hker) := by
    rintro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.map (QuotientGroup.mk' A)) y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A x
    exact ⟨(g : G ⧸ N), by rw [QuotientGroup.lift_mk']; rfl⟩
  exact @Group.isSolvable_of_surjective (G ⧸ N) _ _ _ (QuotientGroup.lift N φ hker) hsurj hsol

end Work.Coprime.SZUtil
