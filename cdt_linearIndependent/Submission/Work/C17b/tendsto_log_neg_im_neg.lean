import Mathlib

namespace Work.C17b

/-- The principal branch of the complex logarithm, restricted to the lower half-plane,
tends to `log t + π·I` as `u → t` (with `t > 0` real): approaching a point `-t` of the
negative real axis from the open upper half-plane, the principal argument tends to `π`. -/
theorem tendsto_log_neg_im_neg {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun u : ℂ => Complex.log (-u)) (nhdsWithin (t : ℂ) {u : ℂ | u.im < 0})
      (nhds ((Real.log t : ℂ) + (Real.pi : ℂ) * Complex.I)) := by
  -- The map `u ↦ -u` sends the lower half-plane (near `t`) into the upper half-plane
  -- (near `-t`), and `-t` is a negative real, where the principal log has a one-sided
  -- limit from the nonnegative imaginary side equal to `log t + π·I`.
  have hzre : (-(t : ℂ)).re < 0 := by rw [Complex.neg_re, Complex.ofReal_re]; linarith
  have hzim : (-(t : ℂ)).im = 0 := by rw [Complex.neg_im, Complex.ofReal_im]; simp
  have hlog := Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hzre hzim
  have hnorm : ‖-(t : ℂ)‖ = t := by rw [norm_neg]; simp [abs_of_pos ht]
  have hcont : ContinuousWithinAt (fun u : ℂ => -u) {u : ℂ | u.im < 0} (t : ℂ) :=
    continuous_neg.continuousAt.continuousWithinAt
  have hmap : Set.MapsTo (fun u : ℂ => -u) {u : ℂ | u.im < 0} {z : ℂ | 0 ≤ z.im} := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    rw [Complex.neg_im]; linarith
  have hneg := hcont.tendsto_nhdsWithin hmap
  have := hlog.comp hneg
  simpa [Function.comp_def, hnorm] using this

end Work.C17b
