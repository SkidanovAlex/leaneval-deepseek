/-
# The right half of the middle socket strip lies in `U₀`

A point `τ` of the strip `-1 < Re τ < 1` with `0 < Re τ` which lies *above* the circle
`|τ|² = Re τ` (i.e. `Re τ ≤ (Re τ)² + (Im τ)²`) is strictly outside the four Farey discs of
radius `1/4` centred at `±1/4` and `±3/4`, hence belongs to `Work.CKFinal.U0`.

Indeed, writing `x = Re τ ≥ 0`, `y = Im τ`:

* `‖τ - 1/4‖² = (x - 1/4)² + y² ≥ (x² + y²) - x/2 + 1/16 ≥ x/2 + 1/16 > 1/16`;
* `‖τ + 1/4‖² = (x + 1/4)² + y² ≥ (x² + y²) + x/2 + 1/16 ≥ 3x/2 + 1/16 > 1/16`;
* `‖τ - 3/4‖² = (x - 3/4)² + y² ≥ (x² + y²) - 3x/2 + 9/16 ≥ (1 - x)/2 + 1/16 > 1/16`
  (this is where `x < 1` is used);
* `‖τ + 3/4‖² = (x + 3/4)² + y² ≥ (x² + y²) + 3x/2 + 9/16 ≥ 5x/2 + 9/16 > 1/16`.

The hypothesis `0 < Re τ` is only needed for the two discs on the left of the strip center and for
the disc at `1/4`; the mirrored statement for `Re τ ≤ 0` is
`Work.CKFinal.Socket.mem_U0_of_re_nonpos`.
-/
import Mathlib
import Submission.Work.CKFinal.U0Defs

noncomputable section

open UpperHalfPlane

namespace Work.CKFinal.Socket

/-! ## Squared distances to the four Farey centers -/

private lemma norm_sub_quarter_sq (x : ℍ) :
    ‖(x : ℂ) - (1 / 4 : ℂ)‖ ^ 2 = (x.re - 1 / 4) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

private lemma norm_add_quarter_sq (x : ℍ) :
    ‖(x : ℂ) + (1 / 4 : ℂ)‖ ^ 2 = (x.re + 1 / 4) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

private lemma norm_sub_threequarter_sq (x : ℍ) :
    ‖(x : ℂ) - (3 / 4 : ℂ)‖ ^ 2 = (x.re - 3 / 4) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

private lemma norm_add_threequarter_sq (x : ℍ) :
    ‖(x : ℂ) + (3 / 4 : ℂ)‖ ^ 2 = (x.re + 3 / 4) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

/-- From `(1/4)² < ‖w‖²` conclude `1/4 < ‖w‖`. -/
private lemma quarter_lt_norm {w : ℂ} (h : (1 / 4 : ℝ) ^ 2 < ‖w‖ ^ 2) : (1 : ℝ) / 4 < ‖w‖ := by
  have h' := sq_lt_sq.mp h
  simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), abs_of_nonneg (norm_nonneg w)] using h'

/-- **The right half of the middle socket strip lies in `U₀`.**  A point `τ` of the strip
`-1 < Re τ < 1` with `0 < Re τ` lying above the circle `|τ|² = Re τ` is strictly outside the four
Farey discs of radius `1/4`. -/
lemma mem_U0_of_re_nonneg {τ : UpperHalfPlane} (hlo : -1 < τ.re) (hhi : τ.re < 1)
    (hpos : 0 < τ.re) (hP : τ.re ≤ τ.re ^ 2 + τ.im ^ 2) : τ ∈ Work.CKFinal.U0 := by
  rw [Work.CKFinal.mem_U0_iff]
  refine ⟨hlo, hhi, ?_, ?_, ?_, ?_⟩
  · -- distance to the center `1/4`
    apply quarter_lt_norm
    rw [norm_sub_quarter_sq τ]
    nlinarith [hP, hpos]
  · -- distance to the center `-1/4`
    apply quarter_lt_norm
    rw [norm_add_quarter_sq τ]
    nlinarith [hP, hpos]
  · -- distance to the center `3/4`: this is where `Re τ < 1` is used
    apply quarter_lt_norm
    rw [norm_sub_threequarter_sq τ]
    nlinarith [hP, hhi]
  · -- distance to the center `-3/4`
    apply quarter_lt_norm
    rw [norm_add_threequarter_sq τ]
    nlinarith [hP, hpos]

end Work.CKFinal.Socket
