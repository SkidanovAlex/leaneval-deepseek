/-
Copyright (c) 2025. All rights reserved.

# The Frattini subgroup of a quotient

For a normal subgroup `M ◁ G` with `M ≤ Φ(G)` we prove

  `Φ(G/M) = Φ(G)M/M = Φ(G).map (QuotientGroup.mk' M)`,

i.e. the Frattini subgroup of the quotient is the image of the Frattini subgroup.

This is the Frattini half of the standard computation
`Φ(G/N) = Φ(G)N/N` for `N ≤ Φ(G)`, which in turn is the key step in the proof that
`Φ(G) < F(G)` for a nontrivial finite solvable group.

The proof rests on the elementary correspondence between the maximal subgroups
(`IsCoatom` in the subgroup lattice) of `G/M` and those maximal subgroups of `G` that contain `M`:
a maximal subgroup `K` of `G` with `M ≤ K` maps onto a maximal subgroup of `G/M`, and every
maximal subgroup of `G/M` arises in this way.  Since `M ≤ Φ(G)` is contained in every maximal
subgroup of `G`, the two lists of coatoms match up and the two Frattini subgroups correspond.

The file is self-contained (only `Mathlib` is imported).
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Fitting

set_option maxHeartbeats 1000000
open scoped Classical

/-- `N ≤ Φ(G)` iff `N` is contained in every maximal subgroup of `G`. -/
theorem le_frattini_iff' {G : Type*} [Group G] {N : Subgroup G} :
    N ≤ frattini G ↔ ∀ K : Subgroup G, IsCoatom K → N ≤ K := by
  constructor
  · intro h K hK; exact h.trans (frattini_le_coatom hK)
  · intro h; simpa [frattini, Order.radical, le_iInf_iff] using h

/-- If `φ : G →* H` is surjective and its kernel is contained in a maximal subgroup `K` of `G`,
then `φ` maps `K` onto a maximal subgroup of `H`.  This is the coatom (maximal-subgroup) part of
the correspondence between the subgroups of `H` and the subgroups of `G` containing `ker φ`. -/
theorem isCoatom_map_of_ker_le {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Surjective φ) {K : Subgroup G} (hker : φ.ker ≤ K) (hK : IsCoatom K) :
    IsCoatom (K.map φ) := by
  refine ⟨?_, ?_⟩
  · -- `K.map φ` is proper, since otherwise `K = ⊤`
    intro htop
    apply hK.1
    rw [← Subgroup.comap_map_eq_self hker, htop, Subgroup.comap_top]
  · -- nothing lies strictly between `K.map φ` and the top
    intro L hL
    have hLmap : (L.comap φ).map φ = L :=
      Subgroup.map_comap_eq_self_of_surjective hφ L
    have hle : K ≤ L.comap φ := Subgroup.map_le_iff_le_comap.mp hL.le
    have hne : K ≠ L.comap φ :=
      fun heq => ne_of_lt hL (by rw [heq, hLmap])
    have hKlt : K < L.comap φ := lt_of_le_of_ne hle hne
    have htop : L.comap φ = ⊤ := hK.2 _ hKlt
    rw [← hLmap, htop, Subgroup.map_top_of_surjective φ hφ]

/-- **The Frattini subgroup of a quotient.**  If `M ◁ G` with `M ≤ Φ(G)`, then
`Φ(G/M) = Φ(G)M/M`, i.e. `Φ(G/M)` is the image of `Φ(G)` under the quotient map. -/
theorem frattini_map_quotient {G : Type*} [Group G] (M : Subgroup G) [M.Normal]
    (hM : M ≤ frattini G) : (frattini G).map (QuotientGroup.mk' M) = frattini (G ⧸ M) := by
  refine le_antisymm ?_ ?_
  · -- `Φ(G)` maps into `Φ(G/M)`, for any normal `M`
    exact Subgroup.map_le_iff_le_comap.mpr
      (frattini_le_comap_frattini_of_surjective (φ := QuotientGroup.mk' M)
        (QuotientGroup.mk'_surjective M))
  · -- conversely `Φ(G/M)` pulls back into `Φ(G)`, using `M ≤ Φ(G)`
    have hcomap : (frattini (G ⧸ M)).comap (QuotientGroup.mk' M) ≤ frattini G := by
      rw [le_frattini_iff']
      intro K hK x hx
      -- `M = ker (mk' M) ≤ Φ(G) ≤ K`, so `K` maps to a maximal subgroup of `G/M`
      have hker : (QuotientGroup.mk' M).ker ≤ K := by
        rw [QuotientGroup.ker_mk']
        exact hM.trans (frattini_le_coatom hK)
      have hKc : IsCoatom (K.map (QuotientGroup.mk' M)) :=
        isCoatom_map_of_ker_le (QuotientGroup.mk'_surjective M) hker hK
      have hmem : QuotientGroup.mk' M x ∈ K.map (QuotientGroup.mk' M) :=
        frattini_le_coatom hKc hx
      obtain ⟨k, hk, hkf⟩ := Subgroup.mem_map.mp hmem
      -- hence `x` and `k` differ by an element of `M ≤ K`
      have hx1 : x * k⁻¹ ∈ (QuotientGroup.mk' M).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkf, mul_inv_cancel]
      have hxk : x * k⁻¹ * k ∈ K := mul_mem (hker hx1) hk
      rwa [show x * k⁻¹ * k = x by group] at hxk
    calc frattini (G ⧸ M)
        = ((frattini (G ⧸ M)).comap (QuotientGroup.mk' M)).map (QuotientGroup.mk' M) :=
          (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M)
            (frattini (G ⧸ M))).symm
      _ ≤ (frattini G).map (QuotientGroup.mk' M) := Subgroup.map_mono hcomap

end Work.Fitting
