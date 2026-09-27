import Mathlib
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Drive.N2Lead.saddleArcs

/-!
# The Möbius pin twist of the saddle packet

The Möbius (opposite-sign) saddle packet replaces the star-shaped polar picture `C₀` of the anchor
level by its image under the slab twist `twistY a' 1`, which is the half turn `(x, y, z) ↦ (-x, y, -z)`
on the slab `y ≤ -a'` and the identity on the slab `y ≥ a'`.  This file proves that this twist
performs exactly the announced move on the two halves of the model pin:

* the conjugate of the model arc `arcZ ηs w` (which carries the *lower* half of the pin: its second
  coordinate is `-Im (arcZ ηs w) ≤ -a'`) is mapped to `-arcZ ηs w`, i.e. the pin is reflected;
* the model arc itself (which carries the *upper* half: its second coordinate is
  `Im (arcZ ηs w) ≥ a'`) is fixed.

The numerical content is `√ηs ≤ Im (arcZ ηs w)`: `arcZ ηs w` is a root of `-ηs + I w`, so
`(Im (arcZ ηs w))² = ηs + (Re (arcZ ηs w))² ≥ ηs`, and `Im (arcZ ηs w) ≥ 0` because it is the real
part of the principal square root of `ηs - w I`.  The hypothesis `2 a' ≤ √ηs` then gives
`a' ≤ √ηs ≤ Im (arcZ ηs w)`, which places the two pin halves in the two rigid slabs of the twist.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-! ## The imaginary part of the model arc -/

/-- The imaginary part of `arcZ η w` is the real part of the principal square root of `η - w I`,
hence nonnegative. -/
lemma arcZ_im_nonneg (η w : ℝ) : 0 ≤ (arcZ η w).im := by
  rw [arcZ, Complex.mul_im]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul]
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  positivity

/-- `arcZ η w` is a root of `-η + I w` (`arcZ_sq`), so its squared imaginary part is
`η + (Re (arcZ η w))²`. -/
lemma arcZ_im_sq (η w : ℝ) : (arcZ η w).im ^ 2 = η + (arcZ η w).re ^ 2 := by
  have h := arcZ_sq_re η w
  rw [pow_two, Complex.mul_re] at h
  linarith

/-- **The imaginary part of the model arc is at least `√η`.** -/
lemma sqrt_le_arcZ_im (η w : ℝ) : Real.sqrt η ≤ (arcZ η w).im := by
  have hle : η ≤ (arcZ η w).im ^ 2 := by
    rw [arcZ_im_sq]
    nlinarith [sq_nonneg (arcZ η w).re]
  calc Real.sqrt η ≤ Real.sqrt ((arcZ η w).im ^ 2) := Real.sqrt_le_sqrt hle
    _ = |(arcZ η w).im| := Real.sqrt_sq_eq_abs _
    _ = (arcZ η w).im := abs_of_nonneg (arcZ_im_nonneg η w)

/-! ## The pin twist -/

/-- The conjugate of the model arc lies in the rigid lower slab of the twist `twistY a' 1`, and the
model arc itself in the rigid upper slab; hence the twist reflects the lower half of the pin and
fixes the upper half. -/
theorem mobiusPinTwist {ηs a' : ℝ} (hηs : 0 < ηs) (ha' : 0 < a')
    (hsmall : 2 * a' ≤ Real.sqrt ηs) (w : ℝ) :
    Work.Drive.N2Lead.twistY a' 1 (Work.Drive.N2.cE3 (star (Work.Drive.N2Lead.arcZ ηs w)))
        = Work.Drive.N2.cE3 (-(Work.Drive.N2Lead.arcZ ηs w)) ∧
      Work.Drive.N2Lead.twistY a' 1 (Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ ηs w))
        = Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ ηs w) := by
  have hsqrt_pos : 0 < Real.sqrt ηs := Real.sqrt_pos.mpr hηs
  have hge : Real.sqrt ηs ≤ (arcZ ηs w).im := sqrt_le_arcZ_im ηs w
  have hvpos : 0 < (arcZ ηs w).im := lt_of_lt_of_le hsqrt_pos hge
  have ha'le : a' ≤ (arcZ ηs w).im := by
    have hsqrt : a' ≤ Real.sqrt ηs := by linarith [hsmall, ha'.le]
    linarith [hge, hvpos]
  constructor
  · -- the conjugate of the arc has second coordinate `-Im (arcZ ηs w) ≤ -a'`
    have hy : (Work.Drive.N2.cE3 (star (arcZ ηs w))) 1 ≤ -a' := by
      simp only [Work.Drive.N2.cE3_apply_one]
      have hst : (star (arcZ ηs w)).im = -(arcZ ηs w).im := by simp
      rw [hst]
      linarith
    rw [twistY_one_of_le ha' hy]
    -- the half turn `(x, y, z) ↦ (-x, y, -z)` sends `cE3 (star z)` to `cE3 (-z)`
    apply eq_of_apply_eq
    intro i
    fin_cases i <;>
      simp [Work.Drive.N2.cE3_apply_zero, Work.Drive.N2.cE3_apply_one,
        Work.Drive.N2.cE3_apply_two]
  · -- the arc has second coordinate `Im (arcZ ηs w) ≥ a'`, so the twist is the identity there
    have hy : a' ≤ (Work.Drive.N2.cE3 (arcZ ηs w)) 1 := by
      simpa using ha'le
    exact twistY_eq_self_of_le ha' hy

end

end Work.Drive.N2Lead
