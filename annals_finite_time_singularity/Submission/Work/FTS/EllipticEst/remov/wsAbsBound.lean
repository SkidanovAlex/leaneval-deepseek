import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem wsAbsBound {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {a b θ₀ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc a b, |g s θ₀| ≤ C := by
  -- The slice `s ↦ g s θ₀` is continuous on the compact interval `[a,b]`.
  have hcont : ContinuousOn (fun s : ℝ => g s θ₀) (Set.Icc a b) := by
    have h1 : ContinuousOn (fun s : ℝ => (s, θ₀)) (Set.Icc a b) := by fun_prop
    have h2 := hg.comp h1 (by
      intro s hs
      rw [Set.mem_prod]
      constructor
      · show 0 < s
        linarith [ha, hs.1]
      · show θ₀ ∈ Set.Ioo 0 (Real.pi / 2)
        exact hθ₀)
    simpa [Function.comp_def, Function.uncurry_apply_pair] using h2
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs
  have h := hC s hs
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

end Work.FTS.EllipticEst.remov
