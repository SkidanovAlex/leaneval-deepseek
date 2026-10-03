import Mathlib
import Submission.Work.PlanarSC.BO.Defs
import Submission.Work.HornSC.CellBoundaryJordan.exists_injective_circle_map_of_grid_cycle

namespace Work.PlanarSC.BO

/-! ## Geometry of the segments of oriented steps

These are the two ingredients that connect the (undirected) segments `adjSeg` of two consecutive
vertices of a cycle with the (oriented) segments `stepSeg` of the steps of the family `A`. -/

/-- An oriented unit step and the undirected segment of its endpoints have the same segment. -/
theorem adjSeg_eq_stepSeg_of_isUnitStep {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (h : Work.HornSC.CellBoundaryJordan.IsUnitStep e) :
    Work.HornSC.CellBoundaryJordan.adjSeg e.1 e.2 =
      Work.HornSC.CellBoundaryJordan.stepSeg e := by
  rcases h with h | h
  · rw [Work.HornSC.CellBoundaryJordan.stepSeg_of_eq_east h]
    show Work.HornSC.CellBoundaryJordan.adjSeg e.1 e.2 = _
    rw [h, Work.HornSC.CellBoundaryJordan.adjSeg_east]
  · rw [Work.HornSC.CellBoundaryJordan.stepSeg_of_eq_north h]
    show Work.HornSC.CellBoundaryJordan.adjSeg e.1 e.2 = _
    rw [h, Work.HornSC.CellBoundaryJordan.adjSeg_north]

theorem adjSeg_eq_stepSeg_of_stepAdj {A : Finset ((ℤ × ℤ) × (ℤ × ℤ))}
    (hunit : ∀ e ∈ A, Work.HornSC.CellBoundaryJordan.IsUnitStep e) {v w : ℤ × ℤ}
    (h : Work.HornSC.CellBoundaryJordan.BO.StepAdj A v w) :
    ∃ e ∈ A, Work.HornSC.CellBoundaryJordan.adjSeg v w =
      Work.HornSC.CellBoundaryJordan.stepSeg e := by
  obtain ⟨e, he, h | h⟩ := h
  · obtain ⟨h1, h2⟩ := h
    refine ⟨e, he, ?_⟩
    rw [← h1, ← h2]
    exact adjSeg_eq_stepSeg_of_isUnitStep (hunit e he)
  · obtain ⟨h1, h2⟩ := h
    refine ⟨e, he, ?_⟩
    have hsym : Work.HornSC.CellBoundaryJordan.adjSeg e.2 e.1 =
        Work.HornSC.CellBoundaryJordan.adjSeg e.1 e.2 := by
      rw [Work.HornSC.CellBoundaryJordan.adjSeg,
        Work.HornSC.CellBoundaryJordan.adjSeg, segment_symm]
    rw [← h2, ← h1, hsym]
    exact adjSeg_eq_stepSeg_of_isUnitStep (hunit e he)

/-- The segment of two vertices joined by a step of `A` is contained in the union of the segments
of the steps of `A`. -/
theorem adjSeg_subset_iUnion_stepSeg {A : Finset ((ℤ × ℤ) × (ℤ × ℤ))}
    (hunit : ∀ e ∈ A, Work.HornSC.CellBoundaryJordan.IsUnitStep e) {v w : ℤ × ℤ}
    (h : Work.HornSC.CellBoundaryJordan.BO.StepAdj A v w) :
    Work.HornSC.CellBoundaryJordan.adjSeg v w ⊆
      ⋃ e ∈ A, Work.HornSC.CellBoundaryJordan.stepSeg e := by
  obtain ⟨e, he, hvw⟩ := adjSeg_eq_stepSeg_of_stepAdj hunit h
  rw [hvw]
  intro z hz
  exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩

/-- Put this in `Submission/Work/PlanarSC/BO/graph_acyclic.lean`, with imports `Mathlib`,
`Submission.Work.PlanarSC.BO.Defs` and
`Submission.Work.HornSC.CellBoundaryJordan.exists_injective_circle_map_of_grid_cycle`, inside
`namespace Work.HornSC.CellBoundaryJordan.BO`.

If the union of the segments of a finite family `A` of unit steps contains no Jordan curve, then the
graph on `stepVerts A` with adjacency `StepAdj A` has no cycle.  Route: for `n ≥ 3` and an injective
`c : ZMod n → ↥(stepVerts A)` with consecutive vertices adjacent, set
`u i = (c (i : ZMod n) : ℤ × ℤ)`; then `u (i+n) = u i`, `u` is injective on `{0,…,n-1}`
(`ZMod.val_natCast_of_lt` / `ZMod.val_injective`) and consecutive vertices are `IsUnitAdj`
(`isUnitAdj_of_stepAdj` from `Defs`).  Apply the sorry-free
`Work.HornSC.CellBoundaryJordan.exists_injective_circle_map_of_grid_cycle` to get an injective
`γ : C(Circle, ℂ)` with `Set.range γ = ⋃ i ∈ {i | i < n}, adjSeg (u i) (u (i+1))`; each
`adjSeg (u i) (u (i+1))` equals `stepSeg e` for the step `e ∈ A` supplied by `StepAdj`, hence
`Set.range γ ⊆ ⋃ e ∈ A, stepSeg e`, contradicting `hno`. -/
theorem graph_acyclic (A : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (hunit : ∀ e ∈ A, Work.HornSC.CellBoundaryJordan.IsUnitStep e)
    (hno : ¬ ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      Set.range γ ⊆ ⋃ e ∈ A, Work.HornSC.CellBoundaryJordan.stepSeg e) :
    ∀ (n : ℕ) (c : ZMod n → ↥(Work.HornSC.CellBoundaryJordan.BO.stepVerts A)), 3 ≤ n →
      Function.Injective c →
      (∀ i, Work.HornSC.CellBoundaryJordan.BO.StepAdj A (c i : ℤ × ℤ) (c (i + 1) : ℤ × ℤ)) →
      False := by
  intro n c hn hcinj hstep
  -- the periodic sequence of vertices of the cycle
  let u : ℕ → ℤ × ℤ := fun i => (c ((i : ℕ) : ZMod n) : ℤ × ℤ)
  have hu : ∀ i, u i = (c ((i : ℕ) : ZMod n) : ℤ × ℤ) := fun i => rfl
  have hper : ∀ i, u (i + n) = u i := by
    intro i
    have hc : (((i + n : ℕ)) : ZMod n) = ((i : ℕ) : ZMod n) := by
      push_cast
      rw [ZMod.natCast_self, add_zero]
    rw [hu, hu, hc]
  have hinj : ∀ i j, i < n → j < n → u i = u j → i = j := by
    intro i j hi hj huv
    have huv' : (c ((i : ℕ) : ZMod n) : ℤ × ℤ) =
        (c ((j : ℕ) : ZMod n) : ℤ × ℤ) := huv
    have hsub : c ((i : ℕ) : ZMod n) = c ((j : ℕ) : ZMod n) := Subtype.ext huv'
    have hc : ((i : ℕ) : ZMod n) = ((j : ℕ) : ZMod n) := hcinj hsub
    have hv := congrArg ZMod.val hc
    rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at hv
    exact hv
  have hstepAdj : ∀ i, i < n →
      Work.HornSC.CellBoundaryJordan.BO.StepAdj A (u i) (u (i + 1)) := by
    intro i _hi
    have h := hstep (((i : ℕ) : ZMod n))
    have hsucc : (((i : ℕ) : ZMod n) + 1) = (((i + 1 : ℕ)) : ZMod n) := by
      push_cast; ring
    rw [hsucc] at h
    exact h
  have hadj : ∀ i, i < n → Work.HornSC.CellBoundaryJordan.IsUnitAdj (u i) (u (i + 1)) :=
    fun i hi => Work.HornSC.CellBoundaryJordan.BO.isUnitAdj_of_stepAdj hunit (hstepAdj i hi)
  -- the cycle spans a Jordan curve contained in the union of the steps of `A`
  obtain ⟨γ, hγinj, hγrange⟩ :=
    Work.HornSC.CellBoundaryJordan.exists_injective_circle_map_of_grid_cycle hn u hper hinj hadj
  refine hno ⟨γ, hγinj, ?_⟩
  rw [hγrange]
  intro z hz
  rw [Set.mem_iUnion] at hz
  obtain ⟨i, hz⟩ := hz
  rw [Set.mem_iUnion] at hz
  obtain ⟨hi, hzi⟩ := hz
  exact adjSeg_subset_iUnion_stepSeg hunit (hstepAdj i hi) hzi

end Work.PlanarSC.BO
