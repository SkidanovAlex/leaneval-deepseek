import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.om1_geometry

/-!
# `Work.A14D.kjn_defs`

Two explicit branches of `log (1 - z)` at the singular point `z = 1` of Zagier's operator `LZ`:

* `kjnMuU z = log (z - 1) - πi` — the branch adapted to the upper half-plane `SU`;
* `kjnMuL z = log (z - 1) + πi` — the branch adapted to the lower half-plane `SL`.

`SU` and `SL` both avoid the ray `(-∞,1]`, so `z - 1 ∈ Complex.slitPlane` there and
`log (z - 1)` is holomorphic; the two branches differ by the constant `-2πi`, and on the unit
disc they both agree with `ell z = log (1 - z)`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- The branch `log (1 - z) = log (z - 1) - π i` on the half-plane `SU`. -/
def kjnMuU (z : ℂ) : ℂ := Complex.log (z - 1) - (Real.pi : ℂ) * Complex.I

/-- The branch `log (1 - z) = log (z - 1) + π i` on the half-plane `SL`. -/
def kjnMuL (z : ℂ) : ℂ := Complex.log (z - 1) + (Real.pi : ℂ) * Complex.I

lemma kjnMuU_sub_kjnMuL (z : ℂ) : kjnMuU z - kjnMuL z = -2 * (Real.pi : ℂ) * Complex.I := by
  simp only [kjnMuU, kjnMuL]; ring

lemma kjnMuU_add_kjnMuL (z : ℂ) : kjnMuU z + kjnMuL z = 2 * Complex.log (z - 1) := by
  simp only [kjnMuU, kjnMuL]; ring

lemma kjn_sub_one_mem_slitPlane {z : ℂ} (hz : z ∈ Om1) : z - 1 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases hz with h | h
  · right
    have him : (z - 1).im = z.im := by simp
    rwa [him]
  · left
    have hre : (z - 1).re = z.re - 1 := Complex.sub_re z 1
    rw [hre]; linarith

lemma kjn_log_sub_one_differentiableOn_Om1 :
    DifferentiableOn ℂ (fun z : ℂ => Complex.log (z - 1)) Om1 := by
  intro z hz
  exact ((Complex.differentiableAt_log (kjn_sub_one_mem_slitPlane hz)).comp z
    (differentiableAt_id.sub_const 1)).differentiableWithinAt

lemma kjnMuU_differentiableOn_SU : DifferentiableOn ℂ kjnMuU SU := by
  unfold kjnMuU
  exact (kjn_log_sub_one_differentiableOn_Om1.mono SU_subset_Om1).sub
    (differentiableOn_const (c := (Real.pi : ℂ) * Complex.I))

lemma kjnMuL_differentiableOn_SL : DifferentiableOn ℂ kjnMuL SL := by
  unfold kjnMuL
  exact (kjn_log_sub_one_differentiableOn_Om1.mono SL_subset_Om1).add
    (differentiableOn_const (c := (Real.pi : ℂ) * Complex.I))

lemma log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * Complex.I := by
  have harg : (-z).arg = z.arg - Real.pi := Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz
  have hnorm : ‖-z‖ = ‖z‖ := norm_neg z
  rw [Complex.log, Complex.log, hnorm, harg]
  push_cast
  ring

lemma log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * Complex.I := by
  have harg : (-z).arg = z.arg + Real.pi := Complex.arg_neg_eq_arg_add_pi_of_im_neg hz
  have hnorm : ‖-z‖ = ‖z‖ := norm_neg z
  rw [Complex.log, Complex.log, hnorm, harg]
  push_cast
  ring

end

end Work.A14D
