import Mathlib
import Submission.Work.HornSC.Tools
import Submission.Work.PlanarSC.not_two_preconnected_pieces_of_two_jordan

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- **Nesting of two disjoint Jordan curves.**  We keep the (statement-identical) target below;
this file contains the proof.

Let `γ, δ : C(Circle, ℂ)` be injective with disjoint ranges (two disjoint Jordan curves) and let
`x` be outside both.  If the connected components of `x` in the complements of the two curves are
both bounded, then the two components are nested.

The proof uses the Jordan separation theorem (`Commons.Topology.Jordan.plane_separation`): the
complement of a Jordan curve has exactly two components `U` (bounded) and `V` (unbounded).  Since
the component of `x` is bounded, `x` must lie in `U` (resp. `U'`), so the two components in the
statement are the bounded ones.  The two curves are connected, so each of them lies entirely in one
of the two components of the other's complement.  If `range δ ⊆ U` and `range γ ⊆ U'` then the two
unbounded components agree and hence so do the curves (`frontier_eq_of_separation`), contradicting
disjointness.  In all remaining cases one of `U ⊆ U'`, `U' ⊆ U` follows by connectedness. -/
theorem subset_or_subset_of_bounded_components {γ δ : C(Circle, ℂ)}
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hdisj : Disjoint (Set.range γ) (Set.range δ))
    {x : ℂ} (hxγ : x ∉ Set.range γ) (hxδ : x ∉ Set.range δ)
    (hbγ : Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x))
    (hbδ : Bornology.IsBounded (connectedComponentIn ((Set.range δ)ᶜ) x)) :
    connectedComponentIn ((Set.range γ)ᶜ) x ⊆ connectedComponentIn ((Set.range δ)ᶜ) x ∨
      connectedComponentIn ((Set.range δ)ᶜ) x ⊆ connectedComponentIn ((Set.range γ)ᶜ) x := by
  classical
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hUVdisj, hUb, hVunb, hUVeq⟩ :=
    Commons.Topology.Jordan.plane_separation γ hγ
  obtain ⟨U', V', hU'o, hV'o, hU'c, hV'c, hU'V'disj, hU'b, hV'unb, hU'V'eq⟩ :=
    Commons.Topology.Jordan.plane_separation δ hδ
  -- `x` lies in the *bounded* component of each complement
  have hxU : x ∈ U := by
    by_contra hxU
    have hxV : x ∈ V := by
      have h : x ∈ U ∪ V := by rw [hUVeq]; exact hxγ
      exact h.resolve_left hxU
    have hcx := Work.PlanarSC.eq_connectedComponentIn_of_separation hγ hVo hUo hVc hUc
      hUVdisj.symm (by rw [Set.union_comm]; exact hUVeq) hxV
    rw [hcx] at hbγ
    exact hVunb hbγ
  have hxU' : x ∈ U' := by
    by_contra hxU'
    have hxV' : x ∈ V' := by
      have h : x ∈ U' ∪ V' := by rw [hU'V'eq]; exact hxδ
      exact h.resolve_left hxU'
    have hcx := Work.PlanarSC.eq_connectedComponentIn_of_separation hδ hV'o hU'o hV'c hU'c
      hU'V'disj.symm (by rw [Set.union_comm]; exact hU'V'eq) hxV'
    rw [hcx] at hbδ
    exact hV'unb hbδ
  -- hence the components in the statement are exactly `U` and `U'`
  have hcxγ : connectedComponentIn ((Set.range γ)ᶜ) x = U :=
    Work.PlanarSC.eq_connectedComponentIn_of_separation hγ hUo hVo hUc hVc hUVdisj hUVeq hxU
  have hcxδ : connectedComponentIn ((Set.range δ)ᶜ) x = U' :=
    Work.PlanarSC.eq_connectedComponentIn_of_separation hδ hU'o hV'o hU'c hV'c
      hU'V'disj hU'V'eq hxU'
  rw [hcxγ, hcxδ]
  -- the two curves are preconnected images of the circle
  have hγpre : IsPreconnected (Set.range γ) := isPreconnected_range γ.continuous
  have hδpre : IsPreconnected (Set.range δ) := isPreconnected_range δ.continuous
  -- the curves cannot be mutually nested
  have hkey : ¬ (Set.range γ ⊆ U' ∧ Set.range δ ⊆ U) := by
    rintro ⟨hγU', hδU⟩
    obtain ⟨hfrontU, hfrontV⟩ :=
      Work.PlanarSC.frontier_eq_of_separation hγ hUo hVo hUc hVc hUVdisj hUVeq
    obtain ⟨hfrontU', hfrontV'⟩ :=
      Work.PlanarSC.frontier_eq_of_separation hδ hU'o hV'o hU'c hV'c hU'V'disj hU'V'eq
    have hVU : V ⊆ V' := by
      have hsub : V ⊆ U' ∪ V' := by
        rw [hU'V'eq]
        intro z hz hzδ
        exact (Set.disjoint_left.mp hUVdisj) (hδU hzδ) hz
      rcases hVc.isPreconnected.subset_or_subset hU'o hV'o hU'V'disj hsub with h | h
      · exact absurd (hU'b.subset h) hVunb
      · exact h
    have hV'V : V' ⊆ V := by
      have hsub : V' ⊆ U ∪ V := by
        rw [hUVeq]
        intro z hz hzγ
        exact (Set.disjoint_left.mp hU'V'disj) (hγU' hzγ) hz
      rcases hV'c.isPreconnected.subset_or_subset hUo hVo hUVdisj hsub with h | h
      · exact absurd (hUb.subset h) hV'unb
      · exact h
    have hVeq : V = V' := Subset.antisymm hVU hV'V
    have hKeq : Set.range γ = Set.range δ := by
      rw [← hfrontV, ← hfrontV', hVeq]
    obtain ⟨w, hw⟩ := Set.range_nonempty γ
    exact (Set.disjoint_left.mp hdisj) hw (hKeq ▸ hw)
  by_cases hP : (U ∩ Set.range δ).Nonempty
  · -- the second curve meets `U`, hence lies in it
    have hδU : Set.range δ ⊆ U := by
      have hsub : Set.range δ ⊆ U ∪ V := by
        intro z hz
        rw [hUVeq]
        exact Set.disjoint_right.mp hdisj hz
      rcases hδpre.subset_or_subset hUo hVo hUVdisj hsub with h | h
      · exact h
      · obtain ⟨z, hzU, hzδ⟩ := hP
        exact absurd (h hzδ) (Set.disjoint_left.mp hUVdisj hzU)
    by_cases hQ : (U' ∩ Set.range γ).Nonempty
    · -- both curves are mutually nested: impossible
      have hγU' : Set.range γ ⊆ U' := by
        have hsub : Set.range γ ⊆ U' ∪ V' := by
          intro z hz
          rw [hU'V'eq]
          exact Set.disjoint_left.mp hdisj hz
        rcases hγpre.subset_or_subset hU'o hV'o hU'V'disj hsub with h | h
        · exact h
        · obtain ⟨z, hzU', hzγ⟩ := hQ
          exact absurd (h hzγ) (Set.disjoint_left.mp hU'V'disj hzU')
      exact absurd ⟨hγU', hδU⟩ hkey
    · -- otherwise `U'` misses the first curve, so `U' ⊆ U`
      have hsub : U' ⊆ U ∪ V := by
        intro z hz
        rw [hUVeq]
        intro hzγ
        exact hQ ⟨z, hz, hzγ⟩
      rcases hU'c.isPreconnected.subset_or_subset hUo hVo hUVdisj hsub with h | h
      · exact Or.inr h
      · exact absurd (h hxU') (Set.disjoint_left.mp hUVdisj hxU)
  · -- `U` misses the second curve, so `U ⊆ U'`
    have hsub : U ⊆ U' ∪ V' := by
      intro z hz
      rw [hU'V'eq]
      intro hzδ
      exact hP ⟨z, hz, hzδ⟩
    rcases hUc.isPreconnected.subset_or_subset hU'o hV'o hU'V'disj hsub with h | h
    · exact Or.inl h
    · exact absurd (h hxU) (Set.disjoint_left.mp hU'V'disj hxU')

end Work.HornSC.CellBoundaryJordan
