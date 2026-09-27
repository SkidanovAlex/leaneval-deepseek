import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace Commons.Analysis.Complex

open AddCircle

/-- The rescaling homeomorphism `AddCircle (2 * π) ≃ₜ AddCircle 1`, followed by multiplication by
`2` in the target, sends `x` to `x / π` modulo `1` (since `2 * (x / (2 * π)) = x / π`).

This is the "undirected direction" `arg / π ∈ ℝ/ℤ` expressed through the angle `arg ∈ ℝ/2πℤ`. -/
private lemma coe_div_pi_eq (x : ℝ) :
    ((x / Real.pi : ℝ) : UnitAddCircle) =
      2 • (homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
        ((x : ℝ) : AddCircle (2 * Real.pi))) := by
  rw [homeomorphAddCircle_apply_mk]
  have h : x / Real.pi = 2 • (x * ((2 * Real.pi)⁻¹ * 1) : ℝ) := by
    rw [two_nsmul]; field_simp; ring
  rw [h, AddCircle.coe_nsmul]

/-- The "undirected direction" of a nonzero complex number, `z ↦ arg z / π ∈ ℝ/ℤ`, is continuous
away from the origin (the jump of `arg` by `2π` across the negative real axis disappears mod `1`). -/
theorem continuousOn_arg_div_pi_coe :
    ContinuousOn (fun z : ℂ => ((z.arg / Real.pi : ℝ) : UnitAddCircle)) {z : ℂ | z ≠ 0} := by
  intro z hz
  -- The continuous map `θ ↦ 2 • θ` on `ℝ/ℤ`, precomposed with the rescaling `ℝ/2πℤ → ℝ/ℤ`,
  -- realises `x ↦ x / π mod 1`.
  have hcont : Continuous (fun θ : Real.Angle =>
      2 • (homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero θ)) :=
    (continuous_nsmul 2).comp
      (homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).continuous
  -- `arg : ℂ → ℝ/2πℤ` is continuous away from the origin.
  have h1 : ContinuousAt (fun w : ℂ => (w.arg : Real.Angle)) z :=
    Complex.continuousAt_arg_coe_angle hz
  refine ((hcont.continuousAt.comp h1).congr ?_).continuousWithinAt
  filter_upwards with w
  exact (coe_div_pi_eq w.arg).symm

end Commons.Analysis.Complex