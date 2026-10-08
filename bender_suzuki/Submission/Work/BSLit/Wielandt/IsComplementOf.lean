import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.BSLit.Wielandt

/-- If `K ⊔ P = ⊤`, `P` normalises `K`, and `K ⊓ P = ⊥`, then `K` and `P` are
complementary subgroups: the multiplication map `K × P → F` is a bijection.

This is the standard semidirect-product decomposition: the hypothesis that `P`
normalises `K` makes the pointwise product set `K * P` a subgroup containing both
`K` and `P`, hence equal to `K ⊔ P = ⊤`; injectivity follows from `K ⊓ P = ⊥`. -/
theorem IsComplementOf {F : Type*} [Group F] (K P : Subgroup F)
    (hsup : K ⊔ P = ⊤)
    (hnorm : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hdisj : K ⊓ P = ⊥) :
    Subgroup.IsComplement' K P := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · exact disjoint_iff.mpr hdisj
  · rw [Set.eq_univ_iff_forall]
    intro g
    let S : Subgroup F :=
      { carrier := (K : Set F) * (P : Set F)
        one_mem' := ⟨1, K.one_mem, 1, P.one_mem, (one_mul 1)⟩
        mul_mem' := by
          rintro a b ⟨k1, hk1, p1, hp1, rfl⟩ ⟨k2, hk2, p2, hp2, rfl⟩
          exact ⟨k1 * (p1 * k2 * p1⁻¹), K.mul_mem hk1 (hnorm p1 hp1 k2 hk2),
            p1 * p2, P.mul_mem hp1 hp2, by group⟩
        inv_mem' := by
          rintro a ⟨k, hk, p, hp, rfl⟩
          exact ⟨p⁻¹ * k⁻¹ * p, by simpa using hnorm p⁻¹ (P.inv_mem hp) k⁻¹ (K.inv_mem hk),
            p⁻¹, P.inv_mem hp, by group⟩ }
    have hS : S = ⊤ := by
      apply le_antisymm le_top
      rw [← hsup]
      apply sup_le
      · intro k hk; exact ⟨k, hk, 1, P.one_mem, (mul_one k)⟩
      · intro p hp; exact ⟨1, K.one_mem, p, hp, (one_mul p)⟩
    have : g ∈ S := by rw [hS]; trivial
    exact this

end Work.BSLit.Wielandt
