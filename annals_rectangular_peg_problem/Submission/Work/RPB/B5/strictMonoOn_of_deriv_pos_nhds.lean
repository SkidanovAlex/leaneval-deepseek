import Mathlib

namespace Work.RPB.B5

/-- If `f : ℝ → ℝ` is continuously differentiable on an open interval about `0`
and its derivative at `0` is positive, then `f` is strictly monotone on some
neighbourhood of `0`.

The proof is the standard one: `deriv f` is continuous at `0`, hence positive on
a neighbourhood of `0`; the mean-value theorem (`strictMonoOn_of_deriv_pos`) then
yields strict monotonicity there. -/
theorem strictMonoOn_of_deriv_pos_nhds (f : ℝ → ℝ) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (hf : ContDiffOn ℝ 1 f (Set.Ioo (-ρ₀) ρ₀)) (hpos : 0 < deriv f 0) :
    ∃ ε : ℝ, 0 < ε ∧ StrictMonoOn f (Set.Ioo (-ε) ε) := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ₀) ρ₀ := ⟨by linarith, by linarith⟩
  -- `deriv f` is continuous at `0`
  have hcontAt : ContinuousAt (deriv f) 0 :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).continuousAt
      (isOpen_Ioo.mem_nhds h0)
  -- hence `deriv f > 0` on a neighbourhood of `0`
  have hev : ∀ᶠ x in nhds (0 : ℝ), 0 < deriv f x :=
    hcontAt.eventually (isOpen_Ioi.mem_nhds hpos)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min δ ρ₀, lt_min hδpos hρ₀, ?_⟩
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · -- `f` is continuous on the smaller interval
    apply hf.continuousOn.mono
    intro x hx
    rw [Set.mem_Ioo] at hx ⊢
    exact ⟨by linarith [hx.1, min_le_right δ ρ₀], by linarith [hx.2, min_le_right δ ρ₀]⟩
  · -- `deriv f > 0` there
    intro x hx
    rw [interior_Ioo, Set.mem_Ioo] at hx
    refine hδ ?_
    rw [Real.dist_eq, sub_zero]
    exact lt_of_lt_of_le (abs_lt.mpr ⟨hx.1, hx.2⟩) (min_le_left δ ρ₀)

end Work.RPB.B5
