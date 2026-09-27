import Mathlib

namespace Work.Surf

-- A uniform separating radius for a finite set: if `Z` is finite and `S p` is an open neighbourhood
-- of `p` for each `p ∈ Z`, then there is a single `r > 0` with `closedBall p r ⊆ S p` for all `p ∈ Z`
-- and with the closed `r`-balls around distinct points of `Z` pairwise disjoint.
-- Proof: pick `ε p > 0` with `closedBall p (ε p) ⊆ S p` for each `p ∈ Z`; the required radius must
-- satisfy `r < ε p` for all `p ∈ Z` and `2 r < dist p q` for all distinct `p, q ∈ Z`.  These are
-- finitely many conditions, so a positive radius below all of them exists (Finset.inf' over the
-- finset of `Z` and over the finset of pairs).
theorem exists_uniform_separating_radius {E : Type*} [MetricSpace E]
    {Z : Set E} (hZ : Z.Finite) (S : E → Set E)
    (hSo : ∀ p ∈ Z, IsOpen (S p)) (hpS : ∀ p ∈ Z, p ∈ S p) :
    ∃ r : ℝ, 0 < r ∧ (∀ p ∈ Z, Metric.closedBall p r ⊆ S p) ∧
      (∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → Disjoint (Metric.closedBall p r) (Metric.closedBall q r)) := by
  classical
  by_cases hZne : Z.Nonempty
  · -- nonempty case: take the minimum of the finitely many constraints and halve it
    have hw : ∀ p ∈ Z, ∃ δ : ℝ, 0 < δ ∧ Metric.closedBall p δ ⊆ S p := by
      intro p hp
      rcases (Metric.isOpen_iff.mp (hSo p hp)) p (hpS p hp) with ⟨ε, hε, hsub⟩
      exact ⟨ε/2, by linarith, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩
    let δ : E → ℝ := fun p => if hp : p ∈ Z then Classical.choose (hw p hp) else 1
    have hδpos : ∀ p ∈ Z, 0 < δ p := by
      intro p hp
      dsimp [δ]
      rw [dif_pos hp]
      exact (Classical.choose_spec (hw p hp)).1
    have hδsub : ∀ p ∈ Z, Metric.closedBall p (δ p) ⊆ S p := by
      intro p hp
      dsimp [δ]
      rw [dif_pos hp]
      exact (Classical.choose_spec (hw p hp)).2
    let T : Finset E := hZ.toFinset
    have hTmem : ∀ p, p ∈ T ↔ p ∈ Z := fun p => Set.Finite.mem_toFinset hZ
    have hTne : T.Nonempty := (Set.Finite.toFinset_nonempty hZ).mpr hZne
    let C : Finset ℝ := (T.image δ) ∪
      (((T ×ˢ T).filter (fun pq : E × E => pq.1 ≠ pq.2)).image (fun pq : E × E => dist pq.1 pq.2 / 2))
    have hCne : C.Nonempty := Finset.Nonempty.mono Finset.subset_union_left (Finset.image_nonempty.mpr hTne)
    let m : ℝ := C.min' hCne
    have hmC : m ∈ C := Finset.min'_mem C hCne
    have hmle : ∀ x ∈ C, m ≤ x := fun x hx => Finset.min'_le C x hx
    have hmpos : 0 < m := by
      rcases Finset.mem_union.mp hmC with hmem | hmem
      · rcases Finset.mem_image.mp hmem with ⟨p, hpT, hpx⟩
        rw [← hpx]
        exact hδpos p ((hTmem p).mp hpT)
      · rcases Finset.mem_image.mp hmem with ⟨pq, hpq, hpqx⟩
        rw [← hpqx]
        rw [Finset.mem_filter] at hpq
        have hne : pq.1 ≠ pq.2 := hpq.2
        have := dist_pos.mpr hne
        linarith
    refine ⟨m/2, by linarith, ?_, ?_⟩
    · intro p hp
      have hpC : δ p ∈ C := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, (hTmem p).mpr hp, rfl⟩)
      have hle : m ≤ δ p := hmle _ hpC
      have : m/2 ≤ δ p := by linarith [hδpos p hp]
      exact (Metric.closedBall_subset_closedBall this).trans (hδsub p hp)
    · intro p hp q hq hpq
      rw [Set.disjoint_left]
      intro x hx hy
      rw [Metric.mem_closedBall] at hx hy
      have hpqC : dist p q / 2 ∈ C := by
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨(p,q), ?_, rfl⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_product.mpr ⟨(hTmem p).mpr hp, (hTmem q).mpr hq⟩, hpq⟩
      have hle : m ≤ dist p q / 2 := hmle _ hpqC
      have hdist : 0 < dist p q := dist_pos.mpr hpq
      have h1 : dist p q ≤ dist x p + dist x q := by
        simpa [dist_comm p x] using dist_triangle p x q
      linarith
  · -- empty case: any positive radius works
    rw [Set.not_nonempty_iff_eq_empty] at hZne
    exact ⟨1, one_pos, by simp [hZne], by simp [hZne]⟩

end Work.Surf
