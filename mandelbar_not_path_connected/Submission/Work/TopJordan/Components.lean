/-
# Components of a complement that splits into two open pieces

Elementary plane-topology lemmas used to read off the two sides of a Jordan curve from
`Commons.Topology.Jordan.plane_separation`.

If `Sᶜ` is the disjoint union of two nonempty open sets `U`, `V`, then

* `Sᶜ` is not preconnected (`not_isPreconnected_compl_of_open_split`);
* a preconnected piece `U` of such a split is exactly the connected component of any of its
  points (`eq_connectedComponentIn_of_open_split`).

Also `exists_norm_ge_of_not_isBounded`, the trivial translation of unboundedness of a subset of
a normed space into "contains points of arbitrarily large norm" in the exact form used by
`Work.Top.JordanForm`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open Set

namespace Work.TopJordan

noncomputable section

/-- **A complement split into two nonempty open pieces is not preconnected.** -/
theorem not_isPreconnected_compl_of_open_split {S U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hd : Disjoint U V) (hUne : U.Nonempty) (hVne : V.Nonempty) (hUV : U ∪ V = Sᶜ) :
    ¬ IsPreconnected Sᶜ := by
  intro hcon
  have h1 : Sᶜ ⊆ U ∪ V := fun z hz => by rw [hUV]; exact hz
  have h2 : Sᶜ ∩ (U ∩ V) = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hd, Set.inter_empty]
  rcases (isPreconnected_iff_subset_of_disjoint.mp hcon) U V hUo hVo h1 h2 with h | h
  · obtain ⟨v, hv⟩ := hVne
    exact Set.disjoint_left.mp hd (h (by rw [← hUV]; exact Or.inr hv)) hv
  · obtain ⟨u, hu⟩ := hUne
    exact Set.disjoint_left.mp hd hu (h (by rw [← hUV]; exact Or.inl hu))

/-- **A piece of an open split is a connected component.**  If `Sᶜ = U ∪ V` with `U`, `V` open
and disjoint and `U` preconnected, then for `u ∈ U` the connected component of `u` in `Sᶜ` is
exactly `U`. -/
theorem eq_connectedComponentIn_of_open_split {S U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hUV : U ∪ V = Sᶜ) (hd : Disjoint U V) (hUpre : IsPreconnected U) {u : ℂ} (hu : u ∈ U) :
    connectedComponentIn Sᶜ u = U := by
  refine Set.Subset.antisymm ?_ ?_
  · have hsub : connectedComponentIn Sᶜ u ⊆ U ∪ V := fun z hz => by
      rw [hUV]; exact connectedComponentIn_subset Sᶜ u hz
    have hdisj : connectedComponentIn Sᶜ u ∩ (U ∩ V) = ∅ := by
      rw [Set.disjoint_iff_inter_eq_empty.mp hd, Set.inter_empty]
    rcases (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn) U V
      hUo hVo hsub hdisj with h | h
    · exact h
    · exact absurd (h (mem_connectedComponentIn (by rw [← hUV]; exact Or.inl hu)))
        (Set.disjoint_left.mp hd hu)
  · exact IsPreconnected.subset_connectedComponentIn hUpre hu
      (fun z hz => by rw [← hUV]; exact Or.inl hz)

/-- **Unboundedness, in the form used by `Work.Top.JordanForm`.** -/
theorem exists_norm_ge_of_not_isBounded {V : Set ℂ} (hV : ¬ Bornology.IsBounded V) (n : ℕ) :
    ∃ z ∈ V, (n : ℝ) ≤ ‖z‖ := by
  by_contra h
  push Not at h
  exact hV (isBounded_iff_forall_norm_le.mpr ⟨(n : ℝ), fun z hz => le_of_lt (h z hz)⟩)

end

end Work.TopJordan
