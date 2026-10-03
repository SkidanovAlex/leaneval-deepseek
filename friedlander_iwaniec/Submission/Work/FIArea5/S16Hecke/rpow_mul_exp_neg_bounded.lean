import Mathlib

namespace Work.FIArea5.S16Hecke

open Filter Set Real

/-- For `c > 0` and `A ≥ 0`, the function `x ↦ x ^ A * exp (-(c * x))` is bounded above on
`[0, ∞)`: it is continuous there (so bounded on any compact subinterval) and tends to `0` at `+∞`. -/
theorem rpow_mul_exp_neg_bounded (c : ℝ) (hc : 0 < c) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → x ^ A * Real.exp (-(c * x)) ≤ C := by
  have hlim : Tendsto (fun x : ℝ => x ^ A * Real.exp (-(c * x))) atTop (nhds 0) := by
    simpa only [neg_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A c hc
  -- Eventually the function is `< 1`.
  have hev : ∀ᶠ x in atTop, x ^ A * Real.exp (-(c * x)) < 1 := by
    have := hlim.eventually (Iio_mem_nhds zero_lt_one)
    simpa [Set.mem_Iio] using this
  rw [Filter.eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  -- Bound on the compact interval `[0, max a 0]`.
  obtain ⟨x₀, _, hx₀max⟩ :
      ∃ x₀ ∈ Set.Icc 0 (max a 0),
        IsMaxOn (fun x : ℝ => x ^ A * Real.exp (-(c * x))) (Set.Icc 0 (max a 0)) x₀ := by
    refine isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, le_max_right _ _⟩ ?_
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun x _ => Or.inr hA)
    · fun_prop
  refine ⟨max 1 (x₀ ^ A * Real.exp (-(c * x₀))), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro x hx
  rcases lt_or_ge x (max a 0) with hxM | hxM
  · exact le_trans (hx₀max ⟨hx, le_of_lt hxM⟩) (le_max_right _ _)
  · have h2 : x ^ A * Real.exp (-(c * x)) < 1 := ha x (le_trans (le_max_left a 0) hxM)
    exact le_trans (le_of_lt h2) (le_max_left _ _)

end Work.FIArea5.S16Hecke
