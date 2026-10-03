import Mathlib

namespace Work.HornFC

/-- Any nonempty open subset of `ℂ` has a connected component (in particular the one
through a given point) containing a nonzero point.  Used to move a base point off `0`. -/
theorem nonzero_mem_component {P : Set ℂ} (hP : IsOpen P) {z : ℂ} (hz : z ∈ P) :
    ∃ w ∈ connectedComponentIn P z, w ≠ 0 := by
  by_cases hz0 : z = 0
  · subst hz0
    obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hP 0 hz
    refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · have hmem : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      exact (Metric.isConnected_ball hεpos).isPreconnected.subset_connectedComponentIn
        (Metric.mem_ball_self hεpos) hball hmem
    · exact Complex.ofReal_ne_zero.mpr (by linarith)
  · exact ⟨z, mem_connectedComponentIn hz, hz0⟩

end Work.HornFC
