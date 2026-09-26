import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

namespace Work.Topology.SphereSlicing

/-- A nonempty preconnected set covered by finitely many pairwise disjoint closed sets is
contained in one of them. -/
theorem preconnected_finite_closed_cover {K : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hK : IsPreconnected K) {ι : Type} [Fintype ι]
    (A : ι → Set LeanEval.KnotTheory.PardonDistortion.R3) (hA : ∀ i : ι, IsClosed (A i))
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (A i) (A j)) (hne : K.Nonempty)
    (hsub : K ⊆ ⋃ i, A i) : ∃ i : ι, K ⊆ A i := by
  classical
  -- Pick a point of `K`; it lies in some member of the cover.
  obtain ⟨x, hxK⟩ := hne
  have hxU : x ∈ ⋃ i, A i := hsub hxK
  rw [Set.mem_iUnion] at hxU
  obtain ⟨i, hxi⟩ := hxU
  refine ⟨i, ?_⟩
  -- The union of all the members other than `i` is again closed.
  have hcomp : IsClosed (⋃ j : {j : ι // j ≠ i}, A j) :=
    isClosed_iUnion_of_finite fun j => hA j.1
  -- Together with `A i` it covers `K`.
  have hcov : K ⊆ A i ∪ ⋃ j : {j : ι // j ≠ i}, A j := by
    intro y hy
    have hyU : y ∈ ⋃ j, A j := hsub hy
    rw [Set.mem_iUnion] at hyU
    obtain ⟨j, hj⟩ := hyU
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  -- The two closed pieces meet `K` in disjoint sets, by pairwise disjointness.
  have hinter : K ∩ (A i ∩ ⋃ j : {j : ι // j ≠ i}, A j) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨y, _hyK, hyi, hyV⟩
    rw [Set.mem_iUnion] at hyV
    obtain ⟨j, hj⟩ := hyV
    exact Set.disjoint_left.mp (hdisj i j.1 j.2.symm) hyi hj
  -- Preconnectedness forces `K` into one of the two closed pieces.
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hK) (A i)
      (⋃ j : {j : ι // j ≠ i}, A j) (hA i) hcomp hcov hinter with h | h
  · exact h
  · -- The second alternative is impossible because `x ∈ K ∩ A i`.
    exfalso
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (h hxK)
    exact Set.disjoint_left.mp (hdisj i j.1 j.2.symm) hxi hj

end Work.Topology.SphereSlicing
