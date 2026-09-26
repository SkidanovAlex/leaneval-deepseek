import Mathlib
import Submission.Work.Topology.SphereSlicing.range_closedCurve_isCompact
import Submission.Work.Smooth.Morse.Defs

/-!
# A connected closed curve inside a finite disjoint union of circles

If a subset `Z` of the surface is a finite disjoint union of (compact, hence closed) curves
(`Work.Smooth.Morse.IsCircleUnion`) and a closed curve `γ` takes all its values in `Z`, then the
image of `γ` — a connected set — lies in one single one of those curves.

The reason is purely topological: a preconnected set covered by finitely many pairwise disjoint
closed sets is contained in one of them
(`exists_subset_of_isPreconnected_iUnion`, proved here from
`isPreconnected_iff_subset_of_disjoint_closed`).
-/

open Set

namespace Work.BoxShrink.Pinch

/-- **A preconnected set covered by finitely many pairwise disjoint closed sets lies in one of
them.** -/
theorem exists_subset_of_isPreconnected_iUnion {α : Type*} [TopologicalSpace α] {ι : Type*}
    [Finite ι] [Nonempty ι] {s : Set α} (hs : IsPreconnected s) (hsne : s.Nonempty)
    (U : ι → Set α) (hUc : ∀ i, IsClosed (U i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hsub : s ⊆ ⋃ i, U i) :
    ∃ i, s ⊆ U i := by
  classical
  obtain ⟨x, hx⟩ := hsne
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp (hsub hx)
  refine ⟨i₀, ?_⟩
  -- the union of all the pieces other than the `i₀`-th one is again closed
  set W : Set α := ⋃ i : ι, (if i = i₀ then (∅ : Set α) else U i) with hW
  have hWclosed : IsClosed W := by
    rw [hW]
    refine isClosed_iUnion_of_finite fun i => ?_
    by_cases h : i = i₀
    · rw [if_pos h]; exact isClosed_empty
    · rw [if_neg h]; exact hUc i
  have hcov : s ⊆ U i₀ ∪ W := by
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hsub hy)
    by_cases h : i = i₀
    · exact Or.inl (by rwa [h] at hi)
    · refine Or.inr ?_
      rw [hW]
      exact Set.mem_iUnion.mpr ⟨i, by rw [if_neg h]; exact hi⟩
  have hdisj' : s ∩ (U i₀ ∩ W) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨y, hys, hy₀, hyW⟩
    rw [hW] at hyW
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hyW
    by_cases h : j = i₀
    · rw [if_pos h] at hj; exact hj
    · rw [if_neg h] at hj
      exact (Set.disjoint_left.mp (hdisj i₀ j (Ne.symm h)) hy₀) hj
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hs (U i₀) W (hUc i₀) hWclosed hcov
    hdisj') with h | h
  · exact h
  · exfalso
    have : x ∈ s ∩ (U i₀ ∩ W) := ⟨hx, hi₀, h hx⟩
    rw [hdisj'] at this
    exact this

/-- **A closed curve whose image lies in a finite disjoint union of circles lies in one of
them.**  The image of `γ` is connected, and each circle is compact (hence closed) by
`Work.Topology.SphereSlicing.range_closedCurve_isCompact`. -/
theorem exists_range_subset_of_isCircleUnion {ψ : Submission.Diffeo} {Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hZ : Work.Smooth.Morse.IsCircleUnion ψ Z)
    (γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ))
    (hγ : ∀ t : ℝ, γ t ∈ Z) :
    ∃ (n : ℕ) (γ₀ : Fin n → Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)),
      Z = ⋃ i, Set.range (γ₀ i).γ ∧ ∃ i : Fin n, Set.range γ.γ ⊆ Set.range (γ₀ i).γ := by
  classical
  obtain ⟨n, γ', _hsimple, hdisj, hZeq⟩ := hZ
  -- there is at least one circle, since `γ` takes values in `Z`
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hmem' : γ 0 ∈ ⋃ i : Fin n, Set.range (γ' i).γ := hZeq ▸ hγ 0
      obtain ⟨i, -⟩ := Set.mem_iUnion.mp hmem'
      exact Fin.elim0 (h ▸ i)
    · exact h
  have hidx : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  refine ⟨n, γ', hZeq, ?_⟩
  have hpre : IsPreconnected (Set.range γ.γ) := isPreconnected_range γ.cont
  have hsne : (Set.range γ.γ).Nonempty := ⟨γ 0, Set.mem_range_self 0⟩
  have hsub : Set.range γ.γ ⊆ ⋃ i : Fin n, Set.range (γ' i).γ := by
    rintro x ⟨t, rfl⟩
    rw [← hZeq]
    exact hγ t
  obtain ⟨i, hi⟩ := exists_subset_of_isPreconnected_iUnion hpre hsne
    (fun i : Fin n => Set.range (γ' i).γ)
    (fun i => (Work.Topology.SphereSlicing.range_closedCurve_isCompact (γ' i)).isClosed)
    hdisj hsub
  exact ⟨i, hi⟩

end Work.BoxShrink.Pinch
