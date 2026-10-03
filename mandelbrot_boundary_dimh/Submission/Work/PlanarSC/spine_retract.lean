import Mathlib
import Submission.Work.PlanarSC.SpineDefs

/-!
# A spine with a building order is a retract of the plane

`Work.PlanarSC.spine S` is the union of the lattice edges of the polyomino `polyK S`.  A
*building order* for the edge family (`Work.PlanarSC.HasBuildingOrder S`) is an enumeration
`f 0, …, f (N-1)` of `gEdges 0 S` in which every edge `f k` with `k ≥ 1` meets the union of its
predecessors `f 0, …, f (k-1)` in exactly one point.

The spine is then the union of the closed segments `edgeSeg f k = [f k.1, f k.2]`, and the
successive intersections are single points, hence closed convex sets.  Borsuk's gluing theorem
for plane retracts (`Commons.Topology.Plane.union_of_retracts`) produces, by induction on the
number of segments, a retraction of `ℂ` onto each partial union, and hence onto the spine.
-/

namespace Work.PlanarSC

open Set

noncomputable section

/-- The `k`-th edge segment of an enumeration `f` of lattice edges. -/
private def edgeSegT (f : ℕ → ℂ × ℂ) (k : ℕ) : Set ℂ := segment ℝ (f k).1 (f k).2

/-- Every lattice edge segment is a closed convex nonempty subset of `ℂ`, hence a retract. -/
private theorem isRetract_edgeSegT (f : ℕ → ℂ × ℂ) (k : ℕ) :
    Commons.Topology.Plane.IsRetract (edgeSegT f k) :=
  Commons.Topology.Plane.convex_retract (convex_segment (f k).1 (f k).2)
    (Commons.Topology.CWComplex.isCompact_segment (f k).1 (f k).2).isClosed
    ⟨(f k).1, left_mem_segment ℝ _ _⟩

/-- The spine of a finite set of cells with a building order is a retract of `ℂ`. -/
theorem spine_retract (S : Finset (ℤ × ℤ)) (h : Work.PlanarSC.HasBuildingOrder S) :
    Commons.Topology.Plane.IsRetract (Work.PlanarSC.spine S) := by
  classical
  obtain ⟨N, f, hN, hcover, hmeet⟩ := h
  -- Step 1: the spine is the union of the first `N` enumerated segments.
  have hspine : Work.PlanarSC.spine S = ⋃ j ∈ Finset.range N, edgeSegT f j := by
    ext z
    constructor
    · intro hz
      rw [Work.PlanarSC.spine] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨e, he, hze⟩ := hz
      obtain ⟨k, hk, hfk⟩ := (hcover e).mp he
      subst hfk
      simp only [Set.mem_iUnion]
      exact ⟨k, Finset.mem_range.mpr hk, hze⟩
    · intro hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨k, hk, hzk⟩ := hz
      have hkN : k < N := Finset.mem_range.mp hk
      have he : f k ∈ Commons.Topology.Plane.gEdges 0 S := (hcover (f k)).mpr ⟨k, hkN, rfl⟩
      rw [Work.PlanarSC.spine]
      simp only [Set.mem_iUnion]
      exact ⟨f k, he, hzk⟩
  rw [hspine]
  -- Step 2: build the partial unions up one segment at a time.
  have key : ∀ n, 1 ≤ n → n ≤ N →
      Commons.Topology.Plane.IsRetract (⋃ j ∈ Finset.range n, edgeSegT f j) := by
    intro n
    induction n with
    | zero => intro h1 _; exact absurd h1 (by omega)
    | succ m ih =>
      intro h1 hmN
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- the first segment
        subst hm0
        have h1' : (⋃ j ∈ Finset.range 1, edgeSegT f j) = edgeSegT f 0 := by
          ext z; simp
        rw [h1']
        exact isRetract_edgeSegT f 0
      · -- glue the `m`-th segment onto the `m` predecessors
        have ih' := ih (by omega) (by omega)
        obtain ⟨p, hp⟩ := hmeet m hmpos (by omega)
        have hcomm : (⋃ j ∈ Finset.range m, edgeSegT f j) =
            ⋃ j : ℕ, ⋃ (_ : j < m), edgeSegT f j := by
          ext z; simp [Finset.mem_range]
        have hInt : (⋃ j ∈ Finset.range m, edgeSegT f j) ∩ edgeSegT f m = {p} := by
          rw [hcomm, Set.inter_comm]
          exact hp
        have hunion : (⋃ j ∈ Finset.range (m + 1), edgeSegT f j) =
            (⋃ j ∈ Finset.range m, edgeSegT f j) ∪ edgeSegT f m := by
          ext z
          simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_range, exists_prop]
          constructor
          · rintro ⟨j, hj, hz⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
            · exact Or.inl ⟨j, hlt, hz⟩
            · exact Or.inr (heq ▸ hz)
          · rintro (⟨j, hj, hz⟩ | hz)
            · exact ⟨j, Nat.lt_succ_of_lt hj, hz⟩
            · exact ⟨m, Nat.lt_succ_self m, hz⟩
        rw [hunion]
        refine Commons.Topology.Plane.union_of_retracts ih'
          (isRetract_edgeSegT f m) ?_
        rw [hInt]
        exact Commons.Topology.Plane.convex_retract (convex_singleton p) isClosed_singleton
          ⟨p, rfl⟩
  exact key N (by omega) (le_refl N)

end

end Work.PlanarSC
