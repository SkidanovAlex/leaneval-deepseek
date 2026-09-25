import Mathlib.GroupTheory.Frattini
import Submission.Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le

namespace Commons.GroupTheory.Frattini

open QuotientGroup

/-- Membership in the Frattini subgroup: an element lies in the intersection of all
maximal subgroups precisely when it lies in every maximal subgroup. -/
lemma mem_frattini_iff {G : Type*} [Group G] (x : G) :
    x ∈ frattini G ↔ ∀ M : Subgroup G, IsCoatom M → x ∈ M := by
  simp [frattini, Order.radical]

/-- If `N ≤ Φ(G)` then the Frattini subgroup of the quotient `G/N` is the image of `Φ(G)`: `Φ(G/N) = Φ(G)·N/N`. -/
theorem frattini_quotient_eq_map {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : N ≤ frattini G) :
    (frattini G).map (QuotientGroup.mk' N) = frattini (G ⧸ N) := by
  let φ : G →* G ⧸ N := QuotientGroup.mk' N
  have hφsurj : Function.Surjective φ := QuotientGroup.mk'_surjective N
  have hker : φ.ker = N := QuotientGroup.ker_mk' (N := N)
  -- It suffices to show that the preimage of `Φ(G/N)` under the quotient map is `Φ(G)`,
  -- since `map ∘ comap` is the identity for surjective maps.
  have hcomap : (frattini (G ⧸ N)).comap φ = frattini G := by
    apply le_antisymm
    · -- an element whose image lies in every maximal subgroup of the quotient lies in
      -- every maximal subgroup of `G`
      intro x hx
      rw [mem_frattini_iff]
      intro M' hM'
      -- `M'` contains the kernel (as it contains `Φ(G) ⊇ N`), hence its image is a
      -- maximal subgroup of the quotient
      have hker_le : φ.ker ≤ M' := by
        rw [hker]
        exact le_trans hN (frattini_le_coatom hM')
      have hM'map : IsCoatom (M'.map φ) :=
        Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le hφsurj hM' hker_le
      have hxφ : φ x ∈ frattini (G ⧸ N) := hx
      have hφxM : φ x ∈ M'.map φ :=
        (mem_frattini_iff (x := φ x)).mp hxφ (M'.map φ) hM'map
      have hxcomap : x ∈ (M'.map φ).comap φ := by simpa using hφxM
      simpa [Subgroup.comap_map_eq_self hker_le] using hxcomap
    · -- the image of the quotient map sends `x ∈ Φ(G)` into every maximal subgroup of
      -- the quotient, by pulling such a maximal subgroup back to `G`
      intro x hx
      simp only [Subgroup.mem_comap]
      rw [mem_frattini_iff]
      intro M hM
      have hMcomap : IsCoatom (M.comap φ) := Subgroup.isCoatom_comap_of_surjective hφsurj hM
      exact (frattini_le_coatom hMcomap) hx
  change (frattini G).map φ = frattini (G ⧸ N)
  rw [← hcomap]
  exact Subgroup.map_comap_eq_self_of_surjective hφsurj (frattini (G ⧸ N))

end Commons.GroupTheory.Frattini