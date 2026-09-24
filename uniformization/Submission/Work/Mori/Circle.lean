import Mathlib
import Submission.Commons.Topology.Winding.hasArg_homotopy_invariant

/-!
# The circle around a point of `ℂ`, and the winding number of its argument

`Work.Mori.circle p r : ℝ → ℂ` is the circle of centre `p` and radius `r`, parametrised with
period `1`:

`circle p r t = p + r * exp (2 π i t)`.

It avoids `p` (for `r ≠ 0`), it is continuous and `1`-periodic, and its argument around `p` is not
periodic — the circle winds once around its centre:
`Work.Mori.not_hasArg_circle` (`Work/Mori/not_hasArg_circle.lean`).

This is the obstruction used in the parabolic case of uniformization: if `X` were biholomorphic to
`ℂ ∖ E` with `E` polar and non-empty, then (by the classical winding argument, see
`Submission/Work/Mori/Argument.lean`) *every* loop of `X` would have a periodic argument around
every point of `E` — in particular the small circle around a point `p ∈ E` that avoids `E`, which is
where `Work.Mori.IsPolar.exists_sphere_eq_empty` is used.
-/

open scoped Topology

noncomputable section

namespace Work.Mori

/-- The circle of centre `p : ℂ` and radius `r : ℝ`, parametrised with period `1`:
`circle p r t = p + r * exp (2 π i t)`. -/
def circle (p : ℂ) (r : ℝ) : ℝ → ℂ :=
  fun t => p + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

theorem circle_zero (p : ℂ) (r : ℝ) : circle p r 0 = p + r := by
  simp [circle]

theorem continuous_circle (p : ℂ) (r : ℝ) : Continuous (circle p r) := by
  unfold circle; fun_prop

theorem circle_periodic (p : ℂ) (r : ℝ) : Function.Periodic (circle p r) 1 := by
  intro t
  have h : Complex.exp (((2 * Real.pi * (t + 1) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨1, ?_⟩
    push_cast
    ring
  simp only [circle]
  rw [h]

/-- The distance from a point of the circle to its centre is the radius. -/
theorem norm_circle_sub (p : ℂ) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : ‖circle p r t - p‖ = r := by
  have h : circle p r t - p = (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    simp [circle]
  rw [h, Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  simp [abs_of_nonneg hr]

/-- A point of the circle is not the centre (for positive radius). -/
theorem circle_ne_center (p : ℂ) {r : ℝ} (hr : 0 < r) (t : ℝ) : circle p r t ≠ p := by
  intro h
  have h1 : ‖circle p r t - p‖ = r := norm_circle_sub p hr.le t
  rw [h, sub_self, norm_zero] at h1
  linarith

/-- `HasArg` for the curve shifted by `-p` is `HasArg` for the curve around `p`. -/
theorem hasArg_shift (f : ℝ → ℂ) (p : ℂ) :
    Commons.Topology.Winding.HasArg (fun t => f t - p) 0 ↔
      Commons.Topology.Winding.HasArg f p := by
  simp only [Commons.Topology.Winding.HasArg, sub_zero]

end Work.Mori
