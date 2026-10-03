import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Horn

/-- A function `E` cannot be constant on a set `C` that is unbounded in the imaginary part while
`satisfying `E w - w → 0` along the upper end of the cylinder: choosing `w ∈ C` with `w.im` very
large forces `E w = c` to be close to `w`, hence `w` to be close to the fixed point `c`. -/
theorem false_of_const_on_upper_unbounded {E : ℂ → ℂ} {C : Set ℂ} {c : ℂ}
    (hC : ∀ M : ℝ, ∃ w ∈ C, M < w.im)
    (hconst : ∀ w ∈ C, E w = c)
    (hE : Filter.Tendsto (fun w : ℂ => E w - w) MandelDim.upperEnd (nhds 0)) : False := by
  -- Along `upperEnd`, eventually `‖E w - w‖ < 1`.
  have hmem : (fun w : ℂ => E w - w) ⁻¹' Metric.ball (0 : ℂ) 1 ∈ MandelDim.upperEnd :=
    hE (Metric.ball_mem_nhds 0 one_pos)
  rw [MandelDim.upperEnd, Filter.mem_comap] at hmem
  obtain ⟨t, ht, hsub⟩ := hmem
  rw [Filter.mem_atTop_sets] at ht
  obtain ⟨a, ha⟩ := ht
  -- Choose `w ∈ C` with imaginary part larger than both `a` and `‖c‖ + 2`.
  obtain ⟨w, hwC, hw⟩ := hC (max a (‖c‖ + 2))
  have hwim : a ≤ w.im := le_trans (le_max_left _ _) (le_of_lt hw)
  have hwbig : ‖c‖ + 2 < w.im := lt_of_le_of_lt (le_max_right _ _) hw
  have h1 : ‖E w - w‖ < 1 := by
    have hmem' := hsub (ha w.im hwim)
    simpa [Metric.mem_ball, dist_eq_norm] using hmem'
  rw [hconst w hwC] at h1
  -- `w` is within distance `1` of `c`, so its imaginary part is bounded.
  have h2 : w.im < ‖c‖ + 1 := by
    have h3 : w.im ≤ ‖w‖ := Complex.im_le_norm w
    have h4 : ‖w‖ ≤ ‖c‖ + ‖c - w‖ := by
      have hweq : w = c - (c - w) := by ring
      calc ‖w‖ = ‖c - (c - w)‖ := congrArg Norm.norm hweq
        _ ≤ ‖c‖ + ‖c - w‖ := norm_sub_le c (c - w)
    linarith
  linarith

end Work.Horn
