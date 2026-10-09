/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exactness of the sequence `Ĥ⁻¹(G,A) → Ĥ⁻¹(G,B) → Ĥ⁻¹(G,C)`

For a short exact sequence of `G`-modules `0 → A → B → C → 0` the induced maps on
`Ĥ⁻¹` satisfy `ker (Ĥ⁻¹(G,B) → Ĥ⁻¹(G,C)) = range (Ĥ⁻¹(G,A) → Ĥ⁻¹(G,B))`.

The content of the verification is that a class in `Ĥ⁻¹(G, B)` which dies in `Ĥ⁻¹(G, C)`
differs from the image of a class in `Ĥ⁻¹(G, A)` by an element of the augmentation submodule,
i.e. represents the same class.
-/
import Mathlib
import Submission.Work.Tate.SES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.Tate

open scoped BigOperators

variable {G : Type u} {A : Type v} {B : Type w} {C : Type x} [Group G] [AddCommGroup A]
  [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
  [DistribMulAction G C]

/-- For a surjective `G`-equivariant additive map the augmentation submodule of the target is the
image of the augmentation submodule of the source. -/
theorem augmentation_map_eq_of_surjective (g : B →+ C)
    (hg : ∀ (γ : G) (b : B), g (γ • b) = γ • g b) (hsurj : Function.Surjective g) :
    (augmentation G B).map g = augmentation G C := by
  refine le_antisymm (map_le_augmentation g hg) ?_
  rw [augmentation, AddSubgroup.closure_le]
  rintro _ ⟨⟨γ, c⟩, rfl⟩
  obtain ⟨d, hd⟩ := hsurj c
  show γ • c - c ∈ ↑(AddSubgroup.map g (augmentation G B))
  rw [← hd, ← hg γ d, ← map_sub]
  exact AddSubgroup.mem_map.mpr ⟨γ • d - d, smul_sub_self_mem_augmentation γ d, rfl⟩

theorem ker_Hm1g_eq_range_Hm1f [Fintype G] (S : SES G A B C) :
    S.Hm1g.ker = S.Hm1f.range := by
  have hmap : (augmentation G B).map S.g = augmentation G C :=
    augmentation_map_eq_of_surjective S.g S.g_equiv S.g_surjective
  refine le_antisymm ?_ ?_
  · -- `ker ⊆ range`
    intro y hy
    rw [AddMonoidHom.mem_ker] at hy
    obtain ⟨b, hb⟩ := Hm1π_surjective y
    rw [← hb] at hy ⊢
    rw [Hm1g_Hm1π, Hm1π_eq_zero_iff, mapKer_apply] at hy
    -- `hy : S.g ↑b ∈ augmentation G C`
    rw [← hmap] at hy
    obtain ⟨w, hw, hgw⟩ := AddSubgroup.mem_map.mp hy
    have hbw : (b : B) - w ∈ S.f.range := by
      rw [S.range_f_eq_ker_g, AddMonoidHom.mem_ker, map_sub, hgw, sub_self]
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hbw
    have haN : a ∈ (norm G A).ker := by
      rw [AddMonoidHom.mem_ker]
      refine S.f_injective ?_
      rw [← norm_map S.f S.f_equiv a, ha, map_sub, b.2,
        norm_eq_zero_of_mem_augmentation hw, sub_zero, map_zero]
    refine ⟨Hm1π G A ⟨a, haN⟩, ?_⟩
    rw [Hm1f_Hm1π, Hm1π_eq_iff, AddSubgroup.mem_comap, map_sub]
    change S.f a - (b : B) ∈ augmentation G B
    rw [ha]
    have hneg : ((b : B) - w) - (b : B) = -w := by abel
    rw [hneg]
    exact neg_mem hw
  · -- `range ⊆ ker`
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    rw [AddMonoidHom.mem_ker]
    refine Hm1_induction_on (C := fun x => S.Hm1g (S.Hm1f x) = 0) x ?_
    intro a
    rw [Hm1f_Hm1π, Hm1g_Hm1π, Hm1π_eq_zero_iff]
    have h0 : (mapKer G B C S.g S.g_equiv (mapKer G A B S.f S.f_equiv a) : C) = 0 := by
      rw [mapKer_apply, mapKer_apply, S.g_comp_f]
    rw [h0]
    exact zero_mem_augmentation

end Work.Tate
