import Mathlib

open NumberField

namespace Work.CMRealSubfield.RootDiscr

/-- If `|disc K| ≤ C ^ d` where `d = [K : ℚ]` and `C > 0`, then the root discriminant
`rootDiscr K = |disc K| ^ (1 / [K : ℚ])` of `K` is at most `C`.

This is the elementary passage from the "discriminant" form of the asymptotic bound to the
"root discriminant" form: raise the inequality to the power `1 / [K : ℚ]`. -/
theorem rootDiscr_le_of_abs_discr_le (K : Type*) [Field K] [NumberField K] {d : ℕ}
    (hd : Module.finrank ℚ K = d) {C : ℝ} (hC : 0 < C)
    (h : |(NumberField.discr K : ℝ)| ≤ C ^ d) : NumberField.rootDiscr K ≤ C := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    rw [hd] at hpos
    exact_mod_cast hpos.ne'
  rw [rootDiscr_def, hd, Int.cast_abs]
  calc |(NumberField.discr K : ℝ)| ^ (d : ℝ)⁻¹
      ≤ (C ^ d) ^ (d : ℝ)⁻¹ := Real.rpow_le_rpow (abs_nonneg _) h (by positivity)
    _ = C := by
        rw [← Real.rpow_natCast C d, ← Real.rpow_mul (le_of_lt hC), mul_inv_cancel₀ hd0,
          Real.rpow_one]

end Work.CMRealSubfield.RootDiscr

/-! The statement is also recorded under the (redundant) nested namespace used by the
delegation skeleton, so that consumers referring to the declaration by either name — in
particular both `Work.CMRealSubfield.RootDiscr.rootDiscr_le_of_abs_discr_le` and
`Work.CMRealSubfield.RootDiscr.Work.CMRealSubfield.RootDiscr.rootDiscr_le_of_abs_discr_le`
— find the same theorem. -/
namespace Work.CMRealSubfield.RootDiscr

namespace Work.CMRealSubfield.RootDiscr

theorem rootDiscr_le_of_abs_discr_le (K : Type*) [Field K] [NumberField K] {d : ℕ}
    (hd : Module.finrank ℚ K = d) {C : ℝ} (hC : 0 < C)
    (h : |(NumberField.discr K : ℝ)| ≤ C ^ d) : NumberField.rootDiscr K ≤ C :=
  _root_.Work.CMRealSubfield.RootDiscr.rootDiscr_le_of_abs_discr_le K hd hC h

end Work.CMRealSubfield.RootDiscr

end Work.CMRealSubfield.RootDiscr
