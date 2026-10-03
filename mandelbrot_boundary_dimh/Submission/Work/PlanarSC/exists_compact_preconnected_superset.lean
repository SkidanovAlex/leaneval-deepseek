import Mathlib
import Submission.Work.PlanarSC.HullDefs

namespace Work.PlanarSC

open Set Metric

/-- A compact subset of an open connected `U ⊆ ℂ` is contained in a compact *preconnected*
`K' ⊆ U`: join the pieces of `K` by paths inside `U`. -/
theorem exists_compact_preconnected_superset {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ K' : Set ℂ, K ⊆ K' ∧ K' ⊆ U ∧ IsCompact K' ∧ K'.Nonempty ∧ IsPreconnected K' := by
  -- `U` is open and connected in `ℂ`, which is locally path connected, hence `U` is path connected.
  have hUpath : IsPathConnected U := (hUo.isConnected_iff_isPathConnected).mp hUc
  rcases eq_empty_or_nonempty K with hKe | hKne
  · -- If `K` is empty a single point of `U` works.
    subst hKe
    obtain ⟨p, hp⟩ := hUc.nonempty
    exact ⟨{p}, empty_subset _, singleton_subset_iff.mpr hp, isCompact_singleton,
      ⟨p, rfl⟩, isPreconnected_singleton⟩
  · -- Cover `K` by finitely many closed balls inside `U`.
    have hrad : ∀ x : K, ∃ r : ℝ, 0 < r ∧ closedBall (x : ℂ) r ⊆ U := by
      intro x
      have hxU : (x : ℂ) ∈ U := hKU x.2
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hxU)
      exact ⟨ε / 2, half_pos hε, fun y hy => hεsub (by
        rw [mem_ball]; rw [mem_closedBall] at hy; linarith)⟩
    choose r hrpos hrsub using hrad
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℂ) (r x))
        (fun _ => isOpen_ball) (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, by
          rw [mem_ball]; simpa using hrpos ⟨z, hz⟩⟩)
    have htne : t.Nonempty := by
      obtain ⟨z, hz⟩ := hKne
      obtain ⟨x, hx, -⟩ := mem_iUnion₂.mp (ht hz)
      exact ⟨x, hx⟩
    obtain ⟨x₀, hx₀⟩ := htne
    have hx₀U : (x₀ : ℂ) ∈ U := hKU x₀.2
    -- Paths inside `U` from every chosen point to the base point `x₀`.
    let J : (x : K) → JoinedIn U (x : ℂ) (x₀ : ℂ) := fun x =>
      hUpath.joinedIn (x : ℂ) (hKU x.2) (x₀ : ℂ) hx₀U
    -- For each chosen point, its closed ball together with the path to `x₀`.
    let S : K → Set ℂ := fun x => closedBall (x : ℂ) (r x) ∪ range (J x).somePath
    let ι := {x : K // x ∈ t}
    let Sf : ι → Set ℂ := fun i => S i.1
    refine ⟨⋃ i : ι, Sf i, ?_, ?_, ?_, ?_, ?_⟩
    · -- `K` is covered by the closed balls.
      intro z hz
      obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (ht hz)
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, Or.inl (ball_subset_closedBall hzx)⟩
    · -- Everything stays inside `U`.
      intro z hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      rcases hi with h | h
      · exact hrsub i.1 h
      · obtain ⟨s, hs⟩ := h
        rw [← hs]; exact (J i.1).somePath_mem s
    · -- A finite union of compact sets is compact.
      apply isCompact_iUnion
      intro i
      exact (isCompact_closedBall _ _).union (isCompact_range (J i.1).somePath.continuous)
    · -- `x₀` lies in the union.
      refine ⟨(x₀ : ℂ), mem_iUnion.mpr ⟨⟨x₀, hx₀⟩, Or.inr ⟨1, ?_⟩⟩⟩
      exact (J x₀).somePath.target
    · -- All the pieces contain `x₀`, so their union is preconnected.
      apply isPreconnected_iUnion
      · refine ⟨(x₀ : ℂ), mem_iInter.mpr fun i => Or.inr ⟨1, ?_⟩⟩
        exact (J i.1).somePath.target
      · intro i
        refine IsPreconnected.union (i.1 : ℂ) ?_ ?_ isPreconnected_closedBall ?_
        · exact mem_closedBall_self (le_of_lt (hrpos i.1))
        · exact ⟨0, (J i.1).somePath.source⟩
        · exact isPreconnected_range (J i.1).somePath.continuous

end Work.PlanarSC
