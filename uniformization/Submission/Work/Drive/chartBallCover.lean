import Mathlib

open Set

namespace Work.Drive

/-- **A countable cover of a nonempty open set by chart balls with compact closures inside it.**
On a complex-charted, locally compact, second countable, Hausdorff space `X`, every nonempty open
set `Y` admits a sequence of points `xs k` and radii `rad k > 0` such that each `chartBall k` is the
image under the inverse of the preferred chart at `xs k` of the euclidean disc of radius `rad k`
about the chart image of `xs k`; each `chartBall k` has compact closure contained in `Y`; and the
chart balls cover `Y`.

Route: for each `y ∈ Y` choose a compact neighbourhood `K y` of `y` with `K y ⊆ Y` (local
compactness, `exists_compact_subset` for the open set `Y`), then `rad y > 0` small enough that the
chart image of `K y` contains the closed disc of radius `rad y`; the sets `B y` form an open cover of
`Y`, and `Y` is Lindelöf (second countability, `isLindelof_univ` with
`IsLindelof.indexed_countable_subcover` applied to the subtype `Y` or directly on `X`), giving a
countable subcover. -/
theorem chartBallCover {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    {Y : Set X} (hY : IsOpen Y) (hYne : Y.Nonempty) :
    ∃ (xs : ℕ → X) (rad : ℕ → ℝ),
      (∀ k, 0 < rad k) ∧
      (∀ k, Metric.ball ((chartAt ℂ (xs k)) (xs k)) (rad k) ⊆ (chartAt ℂ (xs k)).target) ∧
      (∀ k, IsCompact (closure ((chartAt ℂ (xs k)).symm ''
        Metric.ball ((chartAt ℂ (xs k)) (xs k)) (rad k)))) ∧
      (∀ k, closure ((chartAt ℂ (xs k)).symm ''
        Metric.ball ((chartAt ℂ (xs k)) (xs k)) (rad k)) ⊆ Y) ∧
      (⋃ k, (chartAt ℂ (xs k)).symm '' Metric.ball ((chartAt ℂ (xs k)) (xs k)) (rad k)) = Y := by
  classical
  -- For every point of `Y` we produce a compact neighbourhood inside `Y`, contained in the
  -- source of the preferred chart at that point, together with a radius whose closed disc has
  -- chart-inverse image inside that compact set.
  have key : ∀ y : Y, ∃ (r : ℝ) (K : Set X),
      0 < r ∧ IsCompact K ∧ (y : X) ∈ interior K ∧
      K ⊆ Y ∧ K ⊆ (chartAt ℂ (y : X)).source ∧
      Metric.closedBall ((chartAt ℂ (y : X)) (y : X)) r ⊆
        (chartAt ℂ (y : X)) '' interior K := by
    intro y
    obtain ⟨K, hKc, hyK, hKY⟩ := exists_compact_subset
      (hY.inter (chartAt ℂ (y : X)).open_source) ⟨y.2, mem_chart_source ℂ (y : X)⟩
    have hKsrc : K ⊆ (chartAt ℂ (y : X)).source := fun z hz => (hKY hz).2
    have hintsrc : interior K ⊆ (chartAt ℂ (y : X)).source :=
      fun z hz => hKsrc (interior_subset hz)
    have hopen : IsOpen ((chartAt ℂ (y : X)) '' interior K) :=
      (chartAt ℂ (y : X)).isOpen_image_of_subset_source isOpen_interior hintsrc
    have hymem : (chartAt ℂ (y : X)) (y : X) ∈ (chartAt ℂ (y : X)) '' interior K :=
      ⟨(y : X), hyK, rfl⟩
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hopen _ hymem
    exact ⟨ε / 2, K, by linarith, hKc, hyK, fun z hz => (hKY hz).1, hKsrc,
      (Metric.closedBall_subset_ball (by linarith)).trans hεsub⟩
  choose r K hr hKc hyK hKY hKsrc hcd using key
  have hYne_sub : Nonempty Y := hYne.to_subtype
  -- The chart balls.
  let U : Y → Set X := fun y =>
    (chartAt ℂ (y : X)).symm '' Metric.ball ((chartAt ℂ (y : X)) (y : X)) (r y)
  have hUtgt : ∀ y : Y, Metric.ball ((chartAt ℂ (y : X)) (y : X)) (r y) ⊆
      (chartAt ℂ (y : X)).target := by
    intro y
    refine (Metric.ball_subset_closedBall).trans ((hcd y).trans ?_)
    rintro z ⟨x, hx, rfl⟩
    exact (chartAt ℂ (y : X)).map_source (hKsrc y (interior_subset hx))
  have hUo : ∀ y : Y, IsOpen (U y) := fun y =>
    (chartAt ℂ (y : X)).isOpen_image_symm_of_subset_target Metric.isOpen_ball (hUtgt y)
  have hUmem : ∀ y : Y, (y : X) ∈ U y := by
    intro y
    refine ⟨(chartAt ℂ (y : X)) (y : X), Metric.mem_ball_self (hr y), ?_⟩
    exact OpenPartialHomeomorph.left_inv _ (mem_chart_source ℂ (y : X))
  -- The closures of the chart balls stay inside the chosen compact sets.
  have hclK : ∀ y : Y, closure ((chartAt ℂ (y : X)).symm ''
      Metric.ball ((chartAt ℂ (y : X)) (y : X)) (r y)) ⊆ K y := by
    intro y
    refine closure_minimal ?_ (hKc y).isClosed
    rintro z ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (hcd y) (Metric.ball_subset_closedBall hw)
    rw [OpenPartialHomeomorph.left_inv _ (hKsrc y (interior_subset hx))]
    exact interior_subset hx
  -- Lindelöf gives a countable subcover.
  obtain ⟨f, hf⟩ := IsLindelof.indexed_countable_subcover
    (HereditarilyLindelofSpace.isLindelof (Y : Set X)) U hUo
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, hUmem ⟨z, hz⟩⟩)
  refine ⟨fun k => (f k : X), fun k => r (f k), fun k => hr (f k), fun k => hUtgt (f k),
    fun k => (hKc (f k)).of_isClosed_subset isClosed_closure (hclK (f k)),
    fun k => (hclK (f k)).trans (hKY (f k)), ?_⟩
  refine Subset.antisymm ?_ ?_
  · intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    exact hKY (f k) (hclK (f k) (subset_closure hk))
  · intro z hz
    simpa only [U] using hf hz

end Work.Drive
