import Mathlib
import Submission.Work.Mostow.hlDefsAccess
import Submission.Work.Mostow.BaryBase

/-!
# Chart-versus-hyperbolic distance bound near the origin

If `u` and `v` both lie in the hyperbolic ball of radius `δ` about `0` and their Euclidean
(chart) distance is at most `t`, then their hyperbolic distance is at most
`arcosh (1 + 2 cosh δ · t)`.

This is the elementary hyperboloid estimate: writing `hlift u = (u, tpart u)` for the point
of the hyperboloid over `u`, one has the exact identity

`2 (cosh d(u,v) - 1) = ‖u - v‖² - (tpart u - tpart v)²`,

whose right-hand side is at most `‖u - v‖²`.  Since `‖u‖ = sinh (hdist 0 u) ≤ sinh δ` and
similarly for `v`, we get `‖u - v‖ ≤ 2 sinh δ` and hence `‖u - v‖² ≤ 2 sinh δ · t ≤ 2 cosh δ · t`.
-/

set_option linter.unusedVariables false

namespace Work.Mostow

open Submission.Mostow

theorem hdist_le_of_dist_le (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n) {δ t : ℝ}
    (hδ : 0 ≤ δ) (ht : 0 ≤ t) {u v : Submission.Mostow.E n}
    (hu : Submission.Mostow.hdist (0 : Submission.Mostow.E n) u ≤ δ)
    (hv : Submission.Mostow.hdist (0 : Submission.Mostow.E n) v ≤ δ)
    (hd : dist u v ≤ t) :
    Submission.Mostow.hdist u v ≤ Real.arcosh (1 + 2 * Real.cosh δ * t) := by
  have hδsinh : 0 ≤ Real.sinh δ := Real.sinh_nonneg_iff.mpr hδ
  -- chart norms of `u` and `v`
  have hnu : ‖u‖ ≤ Real.sinh δ := by
    rw [← sinh_hdist_zero u]; exact Real.sinh_le_sinh.mpr hu
  have hnv : ‖v‖ ≤ Real.sinh δ := by
    rw [← sinh_hdist_zero v]; exact Real.sinh_le_sinh.mpr hv
  have hnuv : ‖u - v‖ ≤ 2 * Real.sinh δ := by
    calc ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
      _ ≤ Real.sinh δ + Real.sinh δ := add_le_add hnu hnv
      _ = 2 * Real.sinh δ := by ring
  have hnuv_t : ‖u - v‖ ≤ t := by rw [dist_eq_norm] at hd; exact hd
  have hsq : ‖u - v‖ ^ 2 ≤ 2 * (Real.sinh δ * t) := by
    calc ‖u - v‖ ^ 2 = ‖u - v‖ * ‖u - v‖ := by ring
      _ ≤ (2 * Real.sinh δ) * t :=
            mul_le_mul hnuv hnuv_t (norm_nonneg _) (by linarith)
      _ = 2 * (Real.sinh δ * t) := by ring
  -- the exact hyperboloid identity
  have hkey : 2 * (Real.cosh (hdist u v) - 1)
      = ‖u - v‖ ^ 2 - (tpart u - tpart v) ^ 2 := by
    rw [cosh_hdist, norm_sub_sq_real]
    have hu2 := tpart_sq u
    have hv2 := tpart_sq v
    nlinarith [hu2, hv2]
  have hcosh_le : Real.cosh (hdist u v) ≤ 1 + 2 * Real.cosh δ * t := by
    have h1 : Real.cosh (hdist u v) - 1 ≤ Real.sinh δ * t := by
      have h2 : 2 * (Real.cosh (hdist u v) - 1) ≤ 2 * (Real.sinh δ * t) := by
        rw [hkey]
        calc ‖u - v‖ ^ 2 - (tpart u - tpart v) ^ 2 ≤ ‖u - v‖ ^ 2 :=
              by nlinarith [sq_nonneg (tpart u - tpart v)]
          _ ≤ 2 * (Real.sinh δ * t) := hsq
      linarith
    have hst : Real.sinh δ * t ≤ Real.cosh δ * t :=
      mul_le_mul_of_nonneg_right (le_of_lt (Real.sinh_lt_cosh δ)) ht
    have hscale : 1 + Real.cosh δ * t ≤ 1 + 2 * Real.cosh δ * t := by
      have hc : 0 ≤ Real.cosh δ * t := mul_nonneg (le_of_lt (Real.cosh_pos δ)) ht
      nlinarith
    linarith
  -- convert `cosh`-inequality into the `arcosh`-inequality
  have harg : 1 ≤ 1 + 2 * Real.cosh δ * t := by
    have hc : 0 ≤ Real.cosh δ * t := mul_nonneg (le_of_lt (Real.cosh_pos δ)) ht
    nlinarith
  have := (Real.arcosh_le_arcosh (Real.cosh_pos (hdist u v)) (by linarith)).mpr hcosh_le
  rwa [Real.arcosh_cosh (hdist_nonneg u v)] at this

end Work.Mostow
