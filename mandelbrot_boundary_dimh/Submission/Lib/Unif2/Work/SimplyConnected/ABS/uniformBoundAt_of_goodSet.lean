import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.AbsData
import Submission.Lib.Unif2.Work.SimplyConnected.Parabolic.norm_le_of_univalent_normalized
import Submission.Lib.Unif2.UnivalentCompactness

/-!
# The normal-family bound for normalised univalent maps (`Work.SC.UniformBoundAt`)

Hubbard, *Teichmüller theory* Vol. 1, Chapter 1; Anghel–Bruin–Stan, arXiv:2008.12189, Appendix AC.

A family of injective holomorphic maps `ψ : X → ℂ`, holomorphic and injective on open connected
domains `Ω ⊇ U`, normalised by `ψ x₀ = 0` and by the chart derivative
`deriv (ψ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1`, is uniformly bounded on every compact
subset of `U`, by a constant which does not depend on `ψ` or on `Ω`.

The substantive estimate is `Work.SimplyConnected.Parabolic.mem_goodSet_of_mem_closure`: the set
`goodSet x₀ U` of points where the family is bounded on a *neighbourhood* is open, contains `x₀`
(`mem_goodSet_self`), and is closed in `U` (that one propagation step).  Since `U` is connected,
`goodSet x₀ U = U`; compactness of `K` then turns the local bounds into a single one.
-/

namespace Work.SimplyConnected.ABS

open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

/-- The set of points where the family is locally uniformly bounded exhausts a connected `U`. -/
theorem goodSet_eq_of_isConnected {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X} {U : Set X} (hUo : IsOpen U)
    (hUc : IsConnected U) (hx₀ : x₀ ∈ U) {C : ℝ}
    (hC : Work.SimplyConnected.Parabolic.HasGrowthBound C) :
    Work.SimplyConnected.Parabolic.goodSet x₀ U = U := by
  have hGsub : Work.SimplyConnected.Parabolic.goodSet x₀ U ⊆ U := by
    rintro z ⟨V, hVo, hVU, hzV, -⟩
    exact hVU hzV
  refine Set.Subset.antisymm hGsub ?_
  have hne : (Work.SimplyConnected.Parabolic.goodSet x₀ U).Nonempty :=
    ⟨x₀, Work.SimplyConnected.Parabolic.mem_goodSet_self hUo hx₀ hC⟩
  have hdisj : Disjoint (Work.SimplyConnected.Parabolic.goodSet x₀ U)
      (closure (Work.SimplyConnected.Parabolic.goodSet x₀ U))ᶜ :=
    Set.disjoint_left.mpr fun a ha ha' => ha' (subset_closure ha)
  have hsub : U ⊆ Work.SimplyConnected.Parabolic.goodSet x₀ U ∪
      (closure (Work.SimplyConnected.Parabolic.goodSet x₀ U))ᶜ := by
    intro y hy
    by_cases hcl : y ∈ closure (Work.SimplyConnected.Parabolic.goodSet x₀ U)
    · exact Or.inl (Work.SimplyConnected.Parabolic.mem_goodSet_of_mem_closure hUo hC hy hcl)
    · exact Or.inr hcl
  intro z hz
  rcases hUc.2.subset_or_subset (Work.SimplyConnected.Parabolic.isOpen_goodSet x₀ U)
      isClosed_closure.isOpen_compl hdisj hsub with h | h
  · exact h hz
  · exfalso
    obtain ⟨y, hyG⟩ := hne
    exact (h (hGsub hyG)) (subset_closure hyG)

/-- **The normal-family bound for normalised univalent maps.** -/
theorem uniformBoundAt {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (x₀ : X) : Work.SC.UniformBoundAt (X := X) x₀ := by
  obtain ⟨C, hCpos, hCbd⟩ := Submission.exists_growth_bound_normalized_injective
  have hC : Work.SimplyConnected.Parabolic.HasGrowthBound C := ⟨hCpos, hCbd⟩
  intro U hUo hUc hx₀ K hK hKU
  have hgood : Work.SimplyConnected.Parabolic.goodSet x₀ U = U :=
    goodSet_eq_of_isConnected hUo hUc hx₀ hC
  -- each point of `K` has an open neighbourhood in `U` on which the family is bounded
  have hex : ∀ z : ↥K, ∃ V : Set X, IsOpen V ∧ V ⊆ U ∧ (z : X) ∈ V ∧
      Work.SimplyConnected.Parabolic.IsUnifBddOn x₀ U V := by
    intro z
    have hzU : (z : X) ∈ U := hKU z.2
    have hzG : (z : X) ∈ Work.SimplyConnected.Parabolic.goodSet x₀ U := by
      rw [hgood]
      exact hzU
    obtain ⟨V, hVo, hVU, hzV, hbdd⟩ := hzG
    exact ⟨V, hVo, hVU, hzV, hbdd⟩
  choose V hVo hVU hzV hbdd using hex
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVo (fun x hx => by
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact hzV ⟨x, hx⟩)
  -- the bounds of the finitely many members of the cover are added up
  choose B hB0 hBb using hbdd
  refine ⟨t.sum B, ?_⟩
  intro Ω hΩo hΩc hUΩ ψ hψ hinj h0 hder x hxK
  obtain ⟨z, hzt, hxV⟩ : ∃ z ∈ t, x ∈ V z := by
    have hx' : x ∈ ⋃ i ∈ t, V i := ht hxK
    simpa only [Set.mem_iUnion, exists_prop] using hx'
  have h1 : ‖ψ x‖ ≤ B z := hBb z hΩo hΩc hUΩ ψ hψ hinj h0 hder x hxV
  have h2 : B z ≤ t.sum B := Finset.single_le_sum (fun z _ => hB0 z) hzt
  linarith

end

end Work.SimplyConnected.ABS
