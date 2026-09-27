import Mathlib
import Submission.Work.Drive.DegreeTools
import Submission.Work.Drive.UmlaufSetup
import Submission.Work.Drive.arg_div_pi_coe_eq_zero_iff

namespace Work.Drive

/-! # The direction class determines exactly the direction of the line

`Submission.Collision.dirC v = (Complex.arg v / π : ℝ) : ℝ/ℤ` is the *doubled, undirected* direction of
a non-zero vector (`Work.Drive.dirCz` is the same map read on `ℂ`).  Hence two non-zero vectors of the
plane have the same direction class exactly when they are parallel, i.e. one is a non-zero real
multiple of the other.

This is the description used by the signed crossing count of a line with a curve: the crossings of the
line through `p` in direction `u` are exactly the `t` with `dirC (γ t - p) = u`, so that the line (both
rays, not just one) is what the `dirC`-level set of `Work.Drive.winding_eq_crossing_sum` describes.

Proof shape: `dirCz_mul` and `dirCz_inv` (`Drive/DegreeTools`) show that
`dirCz (v * w⁻¹) = dirCz v - dirCz w`, so the equality of the two direction classes is equivalent to
`dirCz (v * w⁻¹) = 0`, and a non-zero complex number has direction class `0` exactly when it is real
(`arg_div_pi_coe_eq_zero_iff`), i.e. `dirCz` only sees the line. -/

open Submission.Collision (dirC)

/-- The vector `ℝ × ℝ` read in `ℂ`: `Submission.Collision.dirC` is `Work.Drive.dirCz` composed with
this identification. -/
lemma toC_eq_mk (p : ℝ × ℝ) : (⟨p.1, p.2⟩ : ℂ) = toC p := by
  apply Complex.ext <;> simp [toC]

/-- `Submission.Collision.dirC` is `Work.Drive.dirCz` read through the identification `ℝ × ℝ ≃ ℂ`. -/
lemma dirC_eq_dirCz (p : ℝ × ℝ) : dirC p = dirCz (toC p) := by
  show ((Complex.arg (⟨p.1, p.2⟩ : ℂ) / Real.pi : ℝ) : UnitAddCircle)
      = ((Complex.arg (toC p) / Real.pi : ℝ) : UnitAddCircle)
  rw [toC_eq_mk p]

/-- The direction class of a real complex number vanishes (`arg` is `0` on the non-negative reals and
`π` on the negative reals). -/
lemma dirCz_ofReal (c : ℝ) : dirCz (c : ℂ) = 0 := by
  show ((Complex.arg (c : ℂ) / Real.pi : ℝ) : UnitAddCircle) = 0
  exact (arg_div_pi_coe_eq_zero_iff (c : ℂ)).mpr (by simp)

/-- **The direction class on `ℂ` classifies the line through the origin**: two non-zero complex
numbers have the same doubled undirected direction exactly when one is a non-zero real multiple of
the other. -/
lemma dirCz_eq_iff_real_smul {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    dirCz z = dirCz w ↔ ∃ c : ℝ, c ≠ 0 ∧ z = (c : ℂ) * w := by
  constructor
  · intro h
    have hwi : w⁻¹ ≠ 0 := inv_ne_zero hw
    have hzw : z * w⁻¹ ≠ 0 := mul_ne_zero hz hwi
    -- The ratio has vanishing direction class, hence is real.
    have h2 : dirCz (z * w⁻¹) = 0 := by
      rw [dirCz_mul hz hwi, dirCz_inv hw, h, add_neg_cancel]
    have him : (z * w⁻¹).im = 0 :=
      (arg_div_pi_coe_eq_zero_iff (z * w⁻¹)).mp h2
    have ht : z * w⁻¹ = (((z * w⁻¹).re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [him]
    refine ⟨(z * w⁻¹).re, ?_, ?_⟩
    · intro hc
      exact hzw (by rw [ht, hc]; simp)
    · have h3 : z * w⁻¹ * w = (((z * w⁻¹).re : ℝ) : ℂ) * w := congrArg (· * w) ht
      rw [mul_assoc, inv_mul_cancel₀ hw, mul_one] at h3
      exact h3
  · rintro ⟨c, hc, hzw⟩
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [hzw, dirCz_mul hcC hw, dirCz_ofReal, zero_add]

/-- **Two non-zero vectors of the plane have the same doubled undirected direction exactly when they
are parallel** (one is a non-zero real multiple of the other). -/
theorem dirC_eq_iff_collinear {v w : ℝ × ℝ} (hv : v ≠ 0) (hw : w ≠ 0) :
    Submission.Collision.dirC v = Submission.Collision.dirC w ↔
      ∃ c : ℝ, c ≠ 0 ∧ v = c • w := by
  rw [dirC_eq_dirCz v, dirC_eq_dirCz w,
    dirCz_eq_iff_real_smul (toC_ne_zero_iff.mpr hv) (toC_ne_zero_iff.mpr hw)]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, toC_injective (h.trans (toC_smul c w).symm)⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, by rw [h, toC_smul]⟩

end Work.Drive
