import Mathlib
import Submission.Work.LinnikAreas.BGTZ.DetContourDefs

namespace Work.LinnikAreas.BGTZ

/-- The Riemann zeta function is bounded on the compact segment
`{1/2 + i t : |t| ≤ 1}` of the critical line.  Indeed `ζ` is continuous away from its
only pole `s = 1`, which the map `t ↦ 1/2 + i t` avoids on `[-1,1]`; the segment is the
continuous image of the compact interval `[-1,1]`. -/
theorem ZetaHalfSmallT :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t| ≤ 1 →
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  -- The map `t ↦ 1/2 + i t` is continuous.
  have hf : Continuous (fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  -- `ζ` composed with it is continuous: the argument never equals its pole `1`.
  have hζ : Continuous (fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    refine ContinuousAt.comp ?_ hf.continuousAt
    apply (differentiableAt_riemannZeta ?_).continuousAt
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  -- A continuous function on the compact interval `[-1,1]` is bounded.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hζ.continuousOn
  refine ⟨max C 1, by positivity, ?_⟩
  intro t ht
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Icc]
    exact abs_le.mp ht
  exact (hC t ht').trans (le_max_left _ _)

end Work.LinnikAreas.BGTZ
