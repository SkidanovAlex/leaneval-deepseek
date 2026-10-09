/-
Copyright (c) 2025. All rights reserved.

# Joining a normal subgroup with a Sylow subgroup when the quotient is a `p`-group

If `M ◁ K` is normal and the quotient `K/M` is a `p`-group, then any Sylow `p`-subgroup `Q` of
`K` satisfies `M ⊔ Q = ⊤`.

The proof is the standard index argument.  The image of `Q` under the quotient map
`K → K ⧸ M` is a Sylow `p`-subgroup of `K ⧸ M` (`Sylow.mapSurjective`), and since `K ⧸ M` is
itself a `p`-group, every such Sylow subgroup is the whole group.  Hence every element of `K`
is congruent modulo `M` to an element of `Q`, i.e. `K = M·Q = M ⊔ Q`.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Fitting

theorem sup_sylow_eq_top_of_isPGroup_quotient {K : Type*} [Group K] [Finite K] (M : Subgroup K)
    [M.Normal] {p : ℕ} [Fact (Nat.Prime p)] (h : IsPGroup p (K ⧸ M)) (Q : Sylow p K) :
    M ⊔ (Q : Subgroup K) = ⊤ := by
  -- The image of `Q` in the quotient is a Sylow `p`-subgroup, and `K ⧸ M` is a `p`-group,
  -- so by maximality that image is everything.
  have htop : (Q : Subgroup K).map (QuotientGroup.mk' M) = ⊤ := by
    have hS : IsPGroup p (⊤ : Subgroup (K ⧸ M)) := h.to_subgroup ⊤
    have hm := (Sylow.mapSurjective (QuotientGroup.mk'_surjective M) Q).is_maximal' hS le_top
    rw [Sylow.coe_mapSurjective] at hm
    exact hm.symm
  rw [eq_top_iff]
  intro g _
  -- `g` is congruent modulo `M` to an element `q` of `Q`.
  have hmem : QuotientGroup.mk' M g ∈ (Q : Subgroup K).map (QuotientGroup.mk' M) := by
    rw [htop]; trivial
  obtain ⟨q, hq, hqg⟩ := Subgroup.mem_map.mp hmem
  have hgm1 : QuotientGroup.mk' M (g * q⁻¹) = 1 := by
    rw [map_mul, map_inv, hqg, mul_inv_cancel]
  have hgm : g * q⁻¹ ∈ M := by
    rw [← QuotientGroup.eq_one_iff (g * q⁻¹)]
    simpa using hgm1
  have : g = (g * q⁻¹) * q := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left hgm) (Subgroup.mem_sup_right hq)

end Work.Fitting
