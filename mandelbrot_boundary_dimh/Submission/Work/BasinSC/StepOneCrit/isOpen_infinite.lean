import Mathlib

namespace Work.BasinSC.StepOneCrit

/-- The complex numbers have no isolated points: a nonempty open subset of `ℂ` contains a ball of
positive radius, which is convex hence preconnected, and nontrivial, hence infinite. -/
theorem isOpen_infinite {U : Set ℂ} (hUo : IsOpen U) (hne : U.Nonempty) : U.Infinite := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hUo z hz
  have hnt : (Metric.ball z ε).Nontrivial := by
    refine ⟨z, ?_, z + ((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · simp [Metric.mem_ball, hεpos]
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      have h1 : ‖((ε / 2 : ℝ) : ℂ)‖ = |ε / 2| := by
        rw [← Real.norm_eq_abs]; simp
      rw [h1, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
      linarith
    · intro hcon
      have hh : ((ε / 2 : ℝ) : ℂ) = 0 := by
        have h := congrArg (fun w : ℂ => w - z) hcon
        simpa using h.symm
      have h2 : ε / 2 = 0 := Complex.ofReal_eq_zero.mp hh
      linarith
  exact Set.Infinite.mono hball ((convex_ball z ε).isPreconnected.infinite_of_nontrivial hnt)

end Work.BasinSC.StepOneCrit
