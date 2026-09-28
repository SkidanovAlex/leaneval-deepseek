import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.goodDefs

namespace Work.RatHurewicz.SkelGraph

-- NOTE: the `Simplicial` scope registers a `|` notation that clashes with the set-builder
-- separator inside `{p : Sigma _ _, _ | ...}`; do not open it here.
open scoped Topology unitInterval

/-- The window of the point at the parameter `s₀` of the arc of index `i`: the set of raw points
which lie on that arc, at a parameter within `ε` of `s₀`. -/
theorem existsOpenArc_aux_window {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    {D : Work.RatHurewicz.MData X n x₀} {i : D.Idx} {s₀ : unitInterval} {ε : ℝ} :
    IsOpen (Sum.inr '' ({p : (Σ _ : D.Idx, unitInterval) |
      p.1 = i ∧ (p.2 : ℝ) ∈ Metric.ball (s₀ : ℝ) ε} : Set (Σ _ : D.Idx, unitInterval))
        : Set (Work.RatHurewicz.Raw D)) := by
  refine isOpenMap_inr _ ?_
  rw [isOpen_sigma_iff]
  intro j
  by_cases hj : j = i
  · rw [hj]
    have hsub : (Sigma.mk i) ⁻¹'
        ({p : (Σ _ : D.Idx, unitInterval) |
            p.1 = i ∧ (p.2 : ℝ) ∈ Metric.ball (s₀ : ℝ) ε} :
          Set (Σ _ : D.Idx, unitInterval)) =
        {t : unitInterval | (t : ℝ) ∈ Metric.ball (s₀ : ℝ) ε} := by
      ext t
      simp
    rw [hsub]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  · have hempty : (Sigma.mk j) ⁻¹'
        ({p : (Σ _ : D.Idx, unitInterval) |
            p.1 = i ∧ (p.2 : ℝ) ∈ Metric.ball (s₀ : ℝ) ε} :
          Set (Σ _ : D.Idx, unitInterval)) = ∅ := by
      ext t
      constructor
      · rintro ⟨hji, -⟩
        exact absurd hji hj
      · intro h
        exact h.elim
    rw [hempty]
    exact isOpen_empty

/-- The point of the arc `i` at the parameter `s₀` belongs to its own window, for `ε > 0`. -/
theorem existsOpenArc_aux_mem {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    {D : Work.RatHurewicz.MData X n x₀} {i : D.Idx} {s₀ : unitInterval} {ε : ℝ} (hε : 0 < ε) :
    (Sum.inr (⟨i, s₀⟩ : Σ _ : D.Idx, unitInterval) : Work.RatHurewicz.Raw D) ∈
      Sum.inr '' ({p : (Σ _ : D.Idx, unitInterval) |
        p.1 = i ∧ (p.2 : ℝ) ∈ Metric.ball (s₀ : ℝ) ε} :
          Set (Σ _ : D.Idx, unitInterval)) :=
  ⟨⟨i, s₀⟩, ⟨rfl, by simpa [Metric.mem_ball] using hε⟩, rfl⟩

/-- Every point of the window of an arc is a point of that arc, at a parameter within `ε` of
`s₀`. -/
theorem existsOpenArc_aux_mem_arc {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    {D : Work.RatHurewicz.MData X n x₀} {i : D.Idx} {s₀ : unitInterval} {ε : ℝ}
    {y : Work.RatHurewicz.Raw D}
    (hy : y ∈ Sum.inr '' ({p : (Σ _ : D.Idx, unitInterval) |
        p.1 = i ∧ (p.2 : ℝ) ∈ Metric.ball (s₀ : ℝ) ε} :
          Set (Σ _ : D.Idx, unitInterval))) :
    ∃ t : unitInterval, (t : ℝ) ∈ Metric.ball (s₀ : ℝ) ε ∧
      y = (Sum.inr (⟨i, t⟩ : Σ _ : D.Idx, unitInterval) : Work.RatHurewicz.Raw D) := by
  obtain ⟨⟨j, t⟩, hp, rfl⟩ := hy
  have hj : j = i := hp.1
  exact ⟨t, hp.2, by rw [hj]⟩

/-- Every low dimensional point of the window of an arc is good. -/
theorem existsOpenArc_aux_good {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    {D : Work.RatHurewicz.MData X n x₀} {U : Set (Work.RatHurewicz.SkelGraph.V D ⊕
      (Work.RatHurewicz.SkelGraph.E D × unitInterval))} {i : D.Idx} {s₀ : unitInterval}
    {ε : ℝ} (hεU : ∀ t : unitInterval, |(t : ℝ) - (s₀ : ℝ)| < ε →
      Sum.inr (Work.RatHurewicz.SkelGraph.eCl D (Sum.inr ⟨i, PUnit.unit⟩), t) ∈ U)
    {y : Work.RatHurewicz.Raw D}
    (hy : y ∈ Sum.inr '' ({p : (Σ _ : D.Idx, unitInterval) |
        p.1 = i ∧ (p.2 : ℝ) ∈ Metric.ball (s₀ : ℝ) ε} :
          Set (Σ _ : D.Idx, unitInterval)))
    (hlow : Work.RatHurewicz.isLowDim D y) :
    y ∈ Work.RatHurewicz.SkelGraph.GoodAux.good D U := by
  obtain ⟨t, ht, rfl⟩ := existsOpenArc_aux_mem_arc hy
  refine ⟨hlow, ?_⟩
  show Sum.inr (Work.RatHurewicz.SkelGraph.eCl D (Sum.inr ⟨i, PUnit.unit⟩), t) ∈ U
  refine hεU t ?_
  rw [Metric.mem_ball, Real.dist_eq] at ht
  exact ht

theorem existsOpenArc {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : Work.RatHurewicz.MData X n x₀)
    {U : Set (Work.RatHurewicz.SkelGraph.V D ⊕
      (Work.RatHurewicz.SkelGraph.E D × unitInterval))}
    (hU : IsOpen U)
    {i : D.Idx} {s₀ : unitInterval}
    (hmem : Sum.inr (Work.RatHurewicz.SkelGraph.eCl D
      (Sum.inr ⟨i, PUnit.unit⟩), s₀) ∈ U) :
    ∃ N : Set (Work.RatHurewicz.Raw D), IsOpen N ∧
      (Sum.inr (⟨i, s₀⟩ : Σ _ : D.Idx, unitInterval) : Work.RatHurewicz.Raw D) ∈ N ∧
      ∀ y' ∈ N, Work.RatHurewicz.isLowDim D y' →
        y' ∈ Work.RatHurewicz.SkelGraph.GoodAux.good D U := by
  obtain ⟨ε, hε, hεU⟩ := GoodAux.exists_nhds_pair hU hmem
  refine ⟨Sum.inr '' ({p : (Σ _ : D.Idx, unitInterval) |
      p.1 = i ∧ (p.2 : ℝ) ∈ Metric.ball (s₀ : ℝ) ε} : Set (Σ _ : D.Idx, unitInterval)),
    existsOpenArc_aux_window, existsOpenArc_aux_mem hε, ?_⟩
  intro y' hy' hlow
  exact existsOpenArc_aux_good hεU hy' hlow

end Work.RatHurewicz.SkelGraph
