import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.NumberField

/-- If `rootDiscr K ≤ C` and `Module.finrank ℚ K = d`, then the absolute
discriminant satisfies `|discr K| ≤ C ^ d` (real numbers, `d` a natural
exponent).

This is the bridge from the root-discriminant formulation of Martinet's
asymptotically-good totally real towers (root discriminants bounded by `C`
along the tower) to the absolute-discriminant bound `|discr K| ≤ C ^ d`.

Proof hints: rewrite `NumberField.rootDiscr_def` and the degree hypothesis;
then `|discr K| = (|discr K| ^ (d⁻¹)) ^ d` by
`Real.rpow_inv_natCast_pow` (base nonnegative, `d ≠ 0` from
`Module.finrank_pos`), and use `pow_le_pow_left₀` with the nonneg base. -/
theorem abs_discr_le_of_rootDiscr_le {K : Type*} [Field K] [NumberField K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) {C : ℝ}
    (hrd : NumberField.rootDiscr K ≤ C) : |(NumberField.discr K : ℝ)| ≤ C ^ d := by
  have hrd' : |(NumberField.discr K : ℝ)| ^ ((d : ℝ)⁻¹) ≤ C := by
    simpa [NumberField.rootDiscr_def, hd] using hrd
  have hΔ0 : 0 ≤ |(NumberField.discr K : ℝ)| := abs_nonneg _
  have hdpos : d ≠ 0 := by
    rw [← hd]
    exact (Module.finrank_pos (R := ℚ) (M := K)).ne'
  calc
    |(NumberField.discr K : ℝ)| = (|(NumberField.discr K : ℝ)| ^ (d : ℝ)⁻¹) ^ d := by
      rw [Real.rpow_inv_natCast_pow hΔ0 hdpos]
    _ ≤ C ^ d := by
      exact pow_le_pow_left₀ (Real.rpow_nonneg hΔ0 _) hrd' d

end Commons.NumberTheory.NumberField