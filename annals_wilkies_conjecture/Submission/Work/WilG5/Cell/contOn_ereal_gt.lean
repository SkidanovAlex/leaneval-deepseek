import Mathlib

namespace Work.WilG5.Cell

theorem contOn_ereal_gt {n : ℕ} {a : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (ha : ContinuousOn a C) {y0 : Fin n → ℝ} (hy0 : y0 ∈ C) {c : ℝ} (h : (c : EReal) < a y0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ C, (∀ i, |y' i - y0 i| < δ) → (c : EReal) < a y' := by
  -- `(c : EReal) < ·` cuts out an open set of `EReal`
  have hcont := ha.continuousWithinAt hy0
  have hopen : IsOpen (Set.Ioi (c : EReal)) := isOpen_Ioi
  have hmem : Set.Ioi (c : EReal) ∈ nhds (a y0) := hopen.mem_nhds h
  -- continuity at `y0` within `C` pulls it back to a relative neighbourhood of `y0`
  have hpre : a ⁻¹' (Set.Ioi (c : EReal)) ∈ nhdsWithin y0 C := hcont hmem
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hpre
  obtain ⟨u, hu, hsub⟩ := hpre
  -- an arbitrary neighbourhood of `y0` in the metric space contains a ball
  rw [Metric.mem_nhds_iff] at hu
  obtain ⟨ε, hε, hball⟩ := hu
  refine ⟨ε, hε, ?_⟩
  intro y' hy'C hdist
  exact hsub ⟨hball (by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro i
      simpa [Real.dist_eq] using hdist i), hy'C⟩

end Work.WilG5.Cell
