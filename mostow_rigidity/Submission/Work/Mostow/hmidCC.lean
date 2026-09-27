import Mathlib
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.Hyper

/-!
# The cosh-kernel at the hyperbolic midpoint (area T4: barycentre)

For `y z : E n` the chart midpoint is
`hmid y z = (2 * cosh (hdist y z / 2))⁻¹ • (y + z)`, and for `v : E n` the cosh-kernel
`cc u v = tpart u * tpart v - ⟪u, v⟫ = cosh (hdist u v)` satisfies

`cc (hmid y z) v = (cc y v + cc z v) / (2 * cosh (hdist y z / 2))`.

The reason is that the two hyperboloid lifts add up to `c = 2 cosh (hdist y z / 2)` times the
lift of the midpoint, i.e. `tpart (hmid y z) = (tpart y + tpart z) / c`; the identity for the
spatial coordinates is plain linearity of the inner product.  Note that no hypothesis
`y ≠ z` and no hypothesis `v ∈ Sph n` is needed.
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

variable {n : ℕ}

/-- The double-angle identity `(2 cosh (d / 2)) ^ 2 = 2 + 2 cosh d`: the Minkowski norm of the
sum of two hyperboloid lifts. -/
private theorem hmidCC_cosh_sq (d : ℝ) : 2 * Real.cosh (d / 2) ^ 2 = 1 + Real.cosh d := by
  have h : Real.cosh (2 * (d / 2)) = Real.cosh (d / 2) ^ 2 + Real.sinh (d / 2) ^ 2 :=
    Real.cosh_two_mul (d / 2)
  rw [show 2 * (d / 2) = d from by ring, Real.sinh_sq] at h
  linarith

/-- **The time coordinate of the midpoint.**  With `c = 2 cosh (hdist y z / 2)`, the sum of the
two hyperboloid lifts is `c` times the lift of `hmid y z`, hence the time coordinates match. -/
theorem hmidCC_tpart (y z : E n) :
    tpart (hmid y z) = (tpart y + tpart z) / (2 * Real.cosh (hdist y z / 2)) := by
  set d := hdist y z with hd
  set c := 2 * Real.cosh (d / 2) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hc2 : c ^ 2 = 2 + 2 * Real.cosh d := by
    have h := hmidCC_cosh_sq d
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
  have hmid_eq : hmid y z = c⁻¹ • (y + z) := by rw [hmid, ← hd, ← hc]
  have hpos : 0 ≤ (tpart y + tpart z) / c :=
    div_nonneg (by linarith [tpart_pos y, tpart_pos z]) (le_of_lt hcpos)
  rw [hmid_eq]
  show Real.sqrt (1 + ‖c⁻¹ • (y + z)‖ ^ 2) = (tpart y + tpart z) / c
  rw [hkey, Real.sqrt_sq hpos]

/-- **The spatial coordinates of the midpoint**: linearity of the inner product. -/
theorem hmidCC_inner (y z v : E n) :
    inner ℝ (hmid y z) v =
      (inner ℝ y v + inner ℝ z v) / (2 * Real.cosh (hdist y z / 2)) := by
  rw [hmid, real_inner_smul_left, inner_add_left, div_eq_mul_inv]
  ring

theorem hmidCC (n : ℕ) (y z v : Submission.Mostow.E n) :
    Submission.Mostow.Hyper.cc (Work.Mostow.hmid y z) v =
      (Submission.Mostow.Hyper.cc y v + Submission.Mostow.Hyper.cc z v) /
        (2 * Real.cosh (Submission.Mostow.hdist y z / 2)) := by
  simp only [Hyper.cc, hmidCC_tpart, hmidCC_inner, div_eq_mul_inv]
  ring

end

end Work.Mostow
