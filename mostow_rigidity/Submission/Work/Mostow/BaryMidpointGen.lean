import Mathlib
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.BaryMidpoint
import Submission.Work.Mostow.hmidCC

/-!
# The midpoint of a hyperbolic segment, without the `y ≠ z` hypothesis

`hmid y z = (2 * cosh (hdist y z / 2))⁻¹ • (y + z)` is the midpoint of the hyperbolic segment
joining `y` and `z`: on the hyperboloid, the lifts of `y` and `z` add up to
`c = 2 cosh (hdist y z / 2)` times the lift of `hmid y z`, and `‖h lift y + h lift z‖` (Minkowski)
is exactly `c`.  Consequently the sum of the lifts is `c` times a point of the hyperboloid,
whose chart coordinates are `c⁻¹ (y + z)`; this single identity gives both equidistance
statements and the Busemann-value identity.

The argument is the one of `BaryMidpoint`, which does not in fact use the hypothesis `y ≠ z`;
here the hypothesis is dropped, and the target statement of this file is exactly that.
-/

namespace Work.Mostow

open Submission.Mostow

/-- the double-angle identity in the form needed for the Minkowski norm of the sum of the lifts -/
private theorem cosh_half_sq_gen (d : ℝ) : 2 * Real.cosh (d / 2) ^ 2 = 1 + Real.cosh d := by
  have h : Real.cosh (2 * (d / 2)) = Real.cosh (d / 2) ^ 2 + Real.sinh (d / 2) ^ 2 :=
    Real.cosh_two_mul (d / 2)
  rw [show 2 * (d / 2) = d from by ring, Real.sinh_sq] at h
  linarith

theorem BaryMidpointGen (n : ℕ) (y z : Submission.Mostow.E n) :
    Submission.Mostow.hdist y ((2 * Real.cosh (Submission.Mostow.hdist y z / 2))⁻¹ • (y + z)) = Submission.Mostow.hdist y z / 2 ∧
    Submission.Mostow.hdist z ((2 * Real.cosh (Submission.Mostow.hdist y z / 2))⁻¹ • (y + z)) = Submission.Mostow.hdist y z / 2 ∧
    (∀ ξ ∈ Submission.Mostow.Sph n, Submission.Mostow.tpart ((2 * Real.cosh (Submission.Mostow.hdist y z / 2))⁻¹ • (y + z)) -
        inner ℝ ((2 * Real.cosh (Submission.Mostow.hdist y z / 2))⁻¹ • (y + z)) ξ =
      ((Submission.Mostow.tpart y - inner ℝ y ξ) + (Submission.Mostow.tpart z - inner ℝ z ξ)) / (2 * Real.cosh (Submission.Mostow.hdist y z / 2))) := by
  set d := hdist y z with hd
  set c := 2 * Real.cosh (d / 2) with hc
  have hd0 : 0 ≤ d := by rw [hd]; exact hdist_nonneg y z
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcne : c ≠ 0 := ne_of_gt hcpos
  -- `c ^ 2` is the Minkowski norm squared of the sum of the two lifts
  have hc2 : c ^ 2 = 2 + 2 * Real.cosh d := by
    have h := cosh_half_sq_gen d
    rw [hc]; nlinarith [h]
  have hy2 : ‖y‖ ^ 2 = tpart y ^ 2 - 1 := by linarith [tpart_sq y]
  have hz2 : ‖z‖ ^ 2 = tpart z ^ 2 - 1 := by linarith [tpart_sq z]
  have hinner : inner ℝ y z = tpart y * tpart z - Real.cosh d := by
    have h := cosh_hdist y z
    rw [← hd] at h
    linarith
  have hnorm : ‖y + z‖ ^ 2 = (tpart y + tpart z) ^ 2 - c ^ 2 := by
    rw [norm_add_sq_real, hy2, hz2, hinner, hc2]; ring
  have hnorm2 : ‖c⁻¹ • (y + z)‖ ^ 2 = ‖y + z‖ ^ 2 / c ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
    ring
  have hkey : 1 + ‖c⁻¹ • (y + z)‖ ^ 2 = ((tpart y + tpart z) / c) ^ 2 := by
    rw [hnorm2, hnorm]; field_simp; ring
  -- the midpoint lies on the hyperboloid: its time coordinate is the average of `tpart`s
  have htpm : tpart (c⁻¹ • (y + z)) = (tpart y + tpart z) / c := by
    have hpos : 0 < (tpart y + tpart z) / c := by
      apply div_pos _ hcpos; linarith [tpart_pos y, tpart_pos z]
    rw [tpart, hkey, Real.sqrt_sq (le_of_lt hpos)]
  have hch : Real.cosh (d / 2) * c = 1 + Real.cosh d := by rw [hc]; linarith [cosh_half_sq_gen d]
  refine ⟨?_, ?_, ?_⟩
  · have hinner_y : inner ℝ y (c⁻¹ • (y + z)) =
        ((tpart y ^ 2 - 1) + (tpart y * tpart z - Real.cosh d)) / c := by
      rw [real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, hy2, hinner]
      ring
    have hcosh1 : Real.cosh (hdist y (c⁻¹ • (y + z))) = Real.cosh (d / 2) := by
      rw [cosh_hdist, htpm, hinner_y, ← mul_div_assoc, ← sub_div, div_eq_iff hcne]
      rw [hch]; ring
    calc hdist y (c⁻¹ • (y + z)) = Real.arcosh (Real.cosh (hdist y (c⁻¹ • (y + z)))) :=
          (Real.arcosh_cosh (hdist_nonneg y _)).symm
      _ = Real.arcosh (Real.cosh (d / 2)) := by rw [hcosh1]
      _ = d / 2 := Real.arcosh_cosh (div_nonneg hd0 two_pos.le)
  · have hinner_z : inner ℝ z (c⁻¹ • (y + z)) =
        ((tpart y * tpart z - Real.cosh d) + (tpart z ^ 2 - 1)) / c := by
      rw [real_inner_smul_right, inner_add_right, real_inner_comm y z, real_inner_self_eq_norm_sq,
        hz2, hinner]
      ring
    have hcosh2 : Real.cosh (hdist z (c⁻¹ • (y + z))) = Real.cosh (d / 2) := by
      rw [cosh_hdist, htpm, hinner_z, ← mul_div_assoc, ← sub_div, div_eq_iff hcne]
      rw [hch]; ring
    calc hdist z (c⁻¹ • (y + z)) = Real.arcosh (Real.cosh (hdist z (c⁻¹ • (y + z)))) :=
          (Real.arcosh_cosh (hdist_nonneg z _)).symm
      _ = Real.arcosh (Real.cosh (d / 2)) := by rw [hcosh2]
      _ = d / 2 := Real.arcosh_cosh (div_nonneg hd0 two_pos.le)
  · intro ξ hξ
    rw [htpm, real_inner_smul_left, inner_add_left]
    ring

end Work.Mostow
