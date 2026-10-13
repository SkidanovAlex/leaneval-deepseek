import Mathlib

namespace Work.WilG4c

/-- If `f : X → ℝ` is continuous at `x₀` and satisfies `|f x| ≤ C` on a set `s` that
accumulates at `x₀` (`x₀ ∈ closure s`), then `|f x₀| ≤ C`. -/
lemma abs_le_of_continuousAt_of_mem_closure {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {C : ℝ} {x₀ : X} {s : Set X}
    (hs : x₀ ∈ closure s) (hf : ContinuousAt f x₀) (hb : ∀ x ∈ s, |f x| ≤ C) :
    |f x₀| ≤ C := by
  -- It suffices to show `|f x₀| ≤ C + ε` for every `ε > 0`.
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- The preimage of the ball of radius `ε` around `f x₀` is a neighbourhood of `x₀`.
  have hmem : f ⁻¹' Metric.ball (f x₀) ε ∈ nhds x₀ :=
    hf.preimage_mem_nhds (Metric.ball_mem_nhds (f x₀) hε)
  -- Since `x₀ ∈ closure s`, that neighbourhood meets `s`.
  obtain ⟨y, hyU, hys⟩ := (mem_closure_iff_nhds.mp hs) _ hmem
  have hy1 : |f y - f x₀| < ε := by
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hyU
    exact hyU
  have hy2 : |f y| ≤ C := hb y hys
  have h1 : |f x₀| ≤ |f x₀ - f y| + |f y| := by
    simpa using abs_add_le (f x₀ - f y) (f y)
  have h2 : |f x₀ - f y| = |f y - f x₀| := abs_sub_comm _ _
  linarith

end Work.WilG4c
