import Mathlib
import Submission.Work.Horn.pushdown_lower_end_linear_growth
import Submission.Work.Horn.germF0_base

namespace Work.Horn


noncomputable section

/-- **Fibres of the pushed-down horn map are bounded.**

Let `d : ParabData f₀ D₀` and suppose the lifted horn map `d.E` has a lower-end limit
`d.E w - w → cl` as `Im w → -∞`.  By `pushdown_lower_end_linear_growth` the pushed-down map
`g = pushdown d.E` is asymptotically linear at `∞` with non-zero slope `π(cl) = exp(2πi cl)`:

`‖g ζ - exp(2πi cl) · ζ‖ ≤ ε ‖ζ‖` for `‖ζ‖ ≥ R`.

Consequently every fibre `g ⁻¹' {y}` is contained in a ball of radius `≈ 2‖y‖/‖exp(2πi cl)‖`,
hence bounded.  (The value `π(cl) ≠ 0` is what makes the argument work; it is exactly the
"non-zero slope" of the horn map at the lower end.) -/
theorem pushdown_fiber_bounded {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {cl : ℂ} (hcl : Filter.Tendsto (fun w : ℂ => d.E w - w) MandelDim.lowerEnd (nhds cl)) :
    ∀ y : ℂ, Bornology.IsBounded ((MandelDim.pushdown d.E) ⁻¹' {y}) := by
  intro y
  have hne : MandelDim.piExp cl ≠ 0 := Complex.exp_ne_zero _
  have hpos : 0 < ‖MandelDim.piExp cl‖ := norm_pos_iff.mpr hne
  -- asymptotic linearity at the lower end with a slack of half the slope
  obtain ⟨R, hR⟩ := pushdown_lower_end_linear_growth d hcl
      (‖MandelDim.piExp cl‖ / 2) (by positivity)
  -- the whole fibre sits in one ball
  refine (Metric.isBounded_closedBall (x := (0 : ℂ))
    (r := max R (2 * ‖y‖ / ‖MandelDim.piExp cl‖))).subset ?_
  intro ζ hζ
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hζ
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_cases hcase : ‖ζ‖ < R
  · exact le_trans hcase.le (le_max_left _ _)
  · have hcase' : R ≤ ‖ζ‖ := not_lt.mp hcase
    have hbound : ‖MandelDim.pushdown d.E ζ - MandelDim.piExp cl * ζ‖ ≤
        ‖MandelDim.piExp cl‖ / 2 * ‖ζ‖ := hR ζ hcase'
    rw [hζ] at hbound
    have h1 : ‖MandelDim.piExp cl‖ * ‖ζ‖ ≤ ‖y - MandelDim.piExp cl * ζ‖ + ‖y‖ := by
      calc ‖MandelDim.piExp cl‖ * ‖ζ‖ = ‖MandelDim.piExp cl * ζ‖ := by rw [norm_mul]
        _ = ‖(MandelDim.piExp cl * ζ - y) + y‖ := by ring_nf
        _ ≤ ‖MandelDim.piExp cl * ζ - y‖ + ‖y‖ := norm_add_le _ _
        _ = ‖y - MandelDim.piExp cl * ζ‖ + ‖y‖ := by rw [norm_sub_rev]
    have h3 : ‖MandelDim.piExp cl‖ / 2 * ‖ζ‖ ≤ ‖y‖ := by linarith
    have h4 : ‖ζ‖ ≤ 2 * ‖y‖ / ‖MandelDim.piExp cl‖ := by
      rw [le_div_iff₀ hpos]
      linarith
    exact le_trans h4 (le_max_right _ _)

end

end Work.Horn
