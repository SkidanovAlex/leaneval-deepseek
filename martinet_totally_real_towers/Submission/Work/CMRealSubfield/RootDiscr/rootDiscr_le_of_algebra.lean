import Mathlib

open NumberField

namespace Work.CMRealSubfield.RootDiscr

/-- **Root discriminants are monotone under field extensions.** If `E` is a subfield of the
number field `K` (an `E`-algebra structure compatible with the `ℚ`-structures, i.e.
`IsScalarTower ℚ E K`), then `rootDiscr E ≤ rootDiscr K`.

The arithmetic input is Mathlib's relative discriminant formula

`(discr K).natAbs = |N(d_{K/E})| * (discr E).natAbs ^ [K : E]`

(`NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`), which shows that
`(discr E).natAbs ^ [K : E]` divides `(discr K).natAbs`. Taking `[K : ℚ]`-th roots and using the
degree identity `[K : ℚ] = [K : E] * [E : ℚ]` gives `|disc E| ^ (1/[E:ℚ]) ≤ |disc K| ^ (1/[K:ℚ])`,
which is the claim. -/
theorem rootDiscr_le_of_algebra {E K : Type*} [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsScalarTower ℚ E K] :
    NumberField.rootDiscr E ≤ NumberField.rootDiscr K := by
  -- The tower formula for discriminants: `(disc E) ^ [K : E]` divides `disc K`.
  have hformula :=
    NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow E (𝓞 E) K (𝓞 K)
  have hdvd : (NumberField.discr E).natAbs ^ Module.finrank E K ∣ (NumberField.discr K).natAbs :=
    ⟨_, by rw [hformula, mul_comm]⟩
  have hle_nat : (NumberField.discr E).natAbs ^ Module.finrank E K ≤ (NumberField.discr K).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)) hdvd
  have hle_real : ((NumberField.discr E).natAbs : ℝ) ^ Module.finrank E K ≤
      ((NumberField.discr K).natAbs : ℝ) := by
    exact_mod_cast hle_nat
  -- Rewrite the natural absolute values as `|discr ·|`.
  have hle_abs : ((|NumberField.discr E| : ℤ) : ℝ) ^ Module.finrank E K ≤
      ((|NumberField.discr K| : ℤ) : ℝ) := by
    rw [← Nat.cast_natAbs (α := ℝ) (NumberField.discr E),
        ← Nat.cast_natAbs (α := ℝ) (NumberField.discr K)]
    exact hle_real
  have hA0 : (0 : ℝ) ≤ ((|NumberField.discr E| : ℤ) : ℝ) :=
    Int.cast_nonneg (abs_nonneg _)
  have hf : 0 < Module.finrank E K := Module.finrank_pos
  have hk_eq : Module.finrank ℚ K = Module.finrank ℚ E * Module.finrank E K :=
    (Module.finrank_mul_finrank ℚ E K).symm
  have he_pos : 0 < Module.finrank ℚ E := Module.finrank_pos (R := ℚ) (M := E)
  have he0 : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he_pos.ne'
  have hf0 : (Module.finrank E K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  -- `[K : E] / [K : ℚ] = 1 / [E : ℚ]`
  have hexp : (Module.finrank E K : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹ =
      (Module.finrank ℚ E : ℝ)⁻¹ := by
    rw [hk_eq]
    push_cast
    field_simp
  -- Take the `[K : ℚ]`-th root of `|disc E| ^ [K : E] ≤ |disc K|`.
  have hkey : ((|NumberField.discr E| : ℤ) : ℝ) ^ ((Module.finrank ℚ E : ℝ))⁻¹ ≤
      ((|NumberField.discr K| : ℤ) : ℝ) ^ ((Module.finrank ℚ K : ℝ))⁻¹ := by
    have h1 : ((|NumberField.discr E| : ℤ) : ℝ) ^ ((Module.finrank E K : ℝ)) ≤
        ((|NumberField.discr K| : ℤ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact hle_abs
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) h1
      (by positivity : (0 : ℝ) ≤ ((Module.finrank ℚ K : ℝ))⁻¹)
    rw [← Real.rpow_mul hA0, hexp] at h2
    exact h2
  rw [NumberField.rootDiscr_def, NumberField.rootDiscr_def]
  exact hkey

end Work.CMRealSubfield.RootDiscr

/-! The statement is also recorded under the (redundant) nested namespace used by the
delegation skeleton, so that consumers referring to the declaration by either name — in
particular both `Work.CMRealSubfield.RootDiscr.rootDiscr_le_of_algebra` and
`Work.CMRealSubfield.RootDiscr.Work.CMRealSubfield.RootDiscr.rootDiscr_le_of_algebra`
— find the same theorem. -/
namespace Work.CMRealSubfield.RootDiscr

namespace Work.CMRealSubfield.RootDiscr

-- Alias: the same statement under the (doubly nested) namespace in which this file's template
-- declared it, so that either fully qualified name resolves.
/-- For a tower `E ⊆ K` of number fields, `rootDiscr E ≤ rootDiscr K` (alias). -/
theorem rootDiscr_le_of_algebra {E K : Type*} [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsScalarTower ℚ E K] :
    NumberField.rootDiscr E ≤ NumberField.rootDiscr K :=
  _root_.Work.CMRealSubfield.RootDiscr.rootDiscr_le_of_algebra

end Work.CMRealSubfield.RootDiscr

end Work.CMRealSubfield.RootDiscr
