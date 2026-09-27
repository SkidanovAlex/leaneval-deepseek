import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.StabHoroForm
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper

/-!
# The lift of the level-`D` horosphere point over the origin of the flat coordinate

For `ξ ∈ Sph n` and `D > 0`, the point `hptOf ξ 0 D` of `ℍⁿ` at horospherical level `D` at `ξ`
whose flat coordinate is `0` is the multiple `((1 - D²)/(2D)) • ξ` of `ξ`: indeed `hptOf ξ 0 D`
is by definition `((1 + D²‖0‖²)/(2D) - D/2) • ξ + D • 0`, and
`(1 + 0)/(2D) - D/2 = (1 - D²)/(2D)`.

Its lift to the hyperboloid is therefore
`hlift (((1 - D²)/(2D)) • ξ)`, whose spatial part is `((1 - D²)/(2D)) • ξ = ((1 - D²)/(2D)) • theta ξ`
(in the spatial coordinates) and whose time part is
`tpart (((1 - D²)/(2D)) • ξ) = √(1 + ((1 - D²)/(2D))²) = (1 + D²)/(2D)`,
using `‖ξ‖ = 1` and `D > 0`. The right-hand side,
`((1 - D²)/(2D)) • theta ξ + D • hlift 0`, has spatial part `((1 - D²)/(2D)) • ξ` and time part
`(1 - D²)/(2D) + D = (1 + D²)/(2D)` (since `hlift 0` is the unit time vector). This identifies the
two sides coordinatewise.
-/

namespace Work.Mostow

open Submission.Mostow

/-- **The lift of `hptOf ξ 0 D`.** The horosphere point at level `D` at `ξ` over the origin of the
flat coordinate is `((1 - D²)/(2D)) • ξ`, and its lift is
`((1 - D²)/(2D)) • theta ξ + D • hlift 0`. -/
theorem hptOfZeroHlift {n : ℕ} (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (D : ℝ) (hD : 0 < D) :
    Submission.Mostow.hlift (Work.Mostow.hptOf ξ 0 D)
      = ((1 - D ^ 2) / (2 * D)) • Work.Mostow.theta ξ
        + D • Submission.Mostow.hlift (0 : Submission.Mostow.E n) := by
  have hξn : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  -- The point itself: `hptOf ξ 0 D = ((1 - D²)/(2D)) • ξ`.
  have hpt : hptOf ξ 0 D = ((1 - D ^ 2) / (2 * D)) • ξ := by
    rw [hptOf]
    simp only [norm_zero, add_zero, smul_zero]
    congr 1
    field_simp
    ring
  -- The time coordinate of that point.
  have hc : tpart (((1 - D ^ 2) / (2 * D)) • ξ) = (1 + D ^ 2) / (2 * D) := by
    have hnp : ‖((1 - D ^ 2) / (2 * D)) • ξ‖ ^ 2 = ((1 - D ^ 2) / (2 * D)) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, hξn, one_pow, mul_one, sq_abs]
    rw [tpart, hnp]
    have h1 : 1 + ((1 - D ^ 2) / (2 * D)) ^ 2 = ((1 + D ^ 2) / (2 * D)) ^ 2 := by
      field_simp
      ring
    rw [h1, Real.sqrt_sq (by positivity)]
  -- The time coordinates of the two sides agree.
  have hsum : (1 + D ^ 2) / (2 * D) = (1 - D ^ 2) / (2 * D) + D := by
    field_simp
    ring
  rw [hpt]
  funext a
  rcases a with i | j
  · simp [Submission.Mostow.hlift, Work.Mostow.theta]
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [Submission.Mostow.hlift, Sum.elim_inr, Work.Mostow.theta,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, tpart_zero]
    rw [hc, hsum]

end Work.Mostow
