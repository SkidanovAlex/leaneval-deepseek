import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.NC4

/-- Counting lemma: if every element of a set `Z` of a group is a product `x * y` with
`x ∈ X ⊆ S` and `y ∈ Y ⊆ T` (for subgroups `S`, `T` with `S ⊓ T = ⊥`), and conversely every such
product lies in `Z`, then `|Z| = |X| * |Y|` (cardinalities are `Set.ncard`). -/
theorem ncard_mul_decomp {G : Type} [Group G] {S T : Subgroup G} (hinf : S ⊓ T = ⊥)
    {X Y Z : Set G} (hX : X ⊆ S) (hY : Y ⊆ T)
    (hmaps : ∀ x ∈ X, ∀ y ∈ Y, x * y ∈ Z)
    (hdecomp : ∀ z ∈ Z, ∃ x ∈ X, ∃ y ∈ Y, z = x * y) :
    Z.ncard = X.ncard * Y.ncard := by
  -- The multiplication map `(x, y) ↦ x * y` is a bijection `X × Y ≃ Z`: it is injective
  -- because `S ⊓ T = ⊥` (a product `x * y` with `x ∈ S`, `y ∈ T` determines both factors),
  -- and it is surjective onto `Z` by `hdecomp`.
  have h1 : (X ×ˢ Y).ncard = Z.ncard := by
    refine Set.ncard_congr (fun p (_ : p ∈ X ×ˢ Y) => p.1 * p.2) ?_ ?_ ?_
    · rintro ⟨x, y⟩ hp
      exact hmaps x (Set.mem_prod.mp hp).1 y (Set.mem_prod.mp hp).2
    · rintro ⟨x1, y1⟩ ⟨x2, y2⟩ hp hq hpq
      simp only [Set.mem_prod] at hp hq
      have hx1S : x1 ∈ S := hX hp.1
      have hy1T : y1 ∈ T := hY hp.2
      have hx2S : x2 ∈ S := hX hq.1
      have hy2T : y2 ∈ T := hY hq.2
      -- From `x1 * y1 = x2 * y2` we get `x2⁻¹ * x1 = y2 * y1⁻¹`, an element of `S ⊓ T`.
      have heq : x2⁻¹ * x1 = y2 * y1⁻¹ := by
        calc x2⁻¹ * x1 = x2⁻¹ * (x1 * y1) * y1⁻¹ := by group
          _ = x2⁻¹ * (x2 * y2) * y1⁻¹ := by rw [hpq]
          _ = y2 * y1⁻¹ := by group
      have hmemS : x2⁻¹ * x1 ∈ S := S.mul_mem (S.inv_mem hx2S) hx1S
      have hmemT : x2⁻¹ * x1 ∈ T := heq ▸ T.mul_mem hy2T (T.inv_mem hy1T)
      have hone : x2⁻¹ * x1 = 1 := by
        have hmem : x2⁻¹ * x1 ∈ S ⊓ T := Subgroup.mem_inf.mpr ⟨hmemS, hmemT⟩
        rw [hinf] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hx_eq : x2 = x1 := by
        have h := hone
        rwa [inv_mul_eq_one] at h
      have hy_eq : y2 = y1 := by
        have h : y2 * y1⁻¹ = 1 := heq ▸ hone
        rwa [mul_inv_eq_one] at h
      exact Prod.ext hx_eq.symm hy_eq.symm
    · rintro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hdecomp z hz
      exact ⟨(x, y), by simp [hx, hy], rfl⟩
  rw [← h1, Set.ncard_prod]

end Work.NormalComplement.NC4
