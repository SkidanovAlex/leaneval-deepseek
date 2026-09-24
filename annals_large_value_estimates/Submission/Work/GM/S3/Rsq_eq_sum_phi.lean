import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.hhat_defs

/-!
# `‖R(u)‖² = Σ_{t,t' ∈ W} φ(t - t', u)`  (GM (7.2) and the expansion used in §7)

`Rfun W u = Σ_{t ∈ W} |u|^{it}` and `phi τ u = exp(i τ log u) = u^{iτ}`.  For `u > 0` each
summand is `u^{it}`, so expanding `‖R‖² = R · conj R` and using
`conj(u^{it}) = u^{-it}`, `u^{is}·u^{-it} = u^{i(s-t)}` gives the pair expansion
`‖R(u)‖² = Σ_{t,t' ∈ W} u^{i(t-t')} = Σ_{t,t' ∈ W} φ(t - t', u)`.

This is the identity that turns `‖R‖²` into a sum of `|W|²` oscillatory exponentials of
frequency `≤ T` (used for the Fourier decay of bumps times `‖R‖²`, `R_l2`/`R_l4`, §10).
-/

namespace Work.GM.S3

open Complex Finset
open scoped BigOperators

/-- For `u > 0`, the summand `|u|^{it}` of `Rfun` is `phi t u = exp(i t log u)`. -/
theorem cpow_abs_eq_phi {u : ℝ} (hu : 0 < u) (t : ℝ) :
    (((|u| : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ)) = phi t u := by
  rw [abs_of_pos hu, phi, Complex.cpow_def_of_ne_zero (by simp [hu.ne']),
    Complex.ofReal_log hu.le]
  ring_nf

/-- `Rfun W u = Σ_{t ∈ W} phi t u` for `u > 0`. -/
theorem Rfun_eq_sum_phi (W : Finset ℝ) {u : ℝ} (hu : 0 < u) :
    Submission.GM.Rfun W u = ∑ t ∈ W, phi t u := by
  rw [Submission.GM.Rfun]
  exact Finset.sum_congr rfl fun t _ => cpow_abs_eq_phi hu t

/-- `conj (phi t u) = phi (-t) u` (valid for every real `u`, since `log u` is real). -/
theorem star_phi_eq (t u : ℝ) : star (phi t u) = phi (-t) u := by
  rw [phi, phi, star_def, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_I]

/-- `phi s u * phi t u = phi (s + t) u`. -/
theorem phi_mul_eq (s t u : ℝ) : phi s u * phi t u = phi (s + t) u := by
  rw [phi, phi, phi, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `‖Rfun W u‖² = Σ_{t,t' ∈ W} φ(t - t', u)` for `u > 0`. -/
theorem Rsq_eq_sum_phi (W : Finset ℝ) {u : ℝ} (hu : 0 < u) :
    ((‖Submission.GM.Rfun W u‖ ^ 2 : ℝ) : ℂ)
      = ∑ t ∈ W, ∑ t' ∈ W, phi (t - t') u := by
  have hR : Submission.GM.Rfun W u = ∑ t ∈ W, phi t u := Rfun_eq_sum_phi W hu
  have hstar : star (Submission.GM.Rfun W u) = ∑ t ∈ W, phi (-t) u := by
    rw [hR, star_sum]
    exact Finset.sum_congr rfl fun t _ => star_phi_eq t u
  have hkey : ((‖Submission.GM.Rfun W u‖ ^ 2 : ℝ) : ℂ)
      = Submission.GM.Rfun W u * star (Submission.GM.Rfun W u) := by
    rw [star_def, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  rw [hkey, hstar, hR, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
  rw [phi_mul_eq]
  congr 1

end Work.GM.S3
