import Mathlib

open NumberField

namespace Work.CMRealSubfield.RealSubfield

/-- A number field `K` is CM if and only if it is totally complex and its maximal real
subfield `K⁺` has exactly half the degree of `K`.

The class `IsCMField` requires `K` to be a quadratic extension of `K⁺`; the converses uses
the tower formula `[K : ℚ] = [K⁺ : ℚ] · [K : K⁺]` to see that
`2 * [K⁺ : ℚ] = [K : ℚ]` forces `[K : K⁺] = 2`. -/
theorem isCMField_iff_isTotallyComplex_and_finrank (K : Type*) [Field K] [NumberField K] :
    NumberField.IsCMField K ↔
      (NumberField.IsTotallyComplex K ∧
        2 * Module.finrank ℚ (NumberField.maximalRealSubfield K) = Module.finrank ℚ K) := by
  constructor
  · -- A CM-field is totally complex and quadratic over `K⁺`, so the tower formula gives
    -- `[K : ℚ] = [K⁺ : ℚ] * 2`.
    intro h
    refine ⟨h.to_isTotallyComplex, ?_⟩
    have hq := h.is_quadratic
    rw [← Module.finrank_mul_finrank ℚ (NumberField.maximalRealSubfield K) K,
      Algebra.IsQuadraticExtension.finrank_eq_two (NumberField.maximalRealSubfield K) K, mul_comm]
  · -- Conversely `2 * [K⁺ : ℚ] = [K : ℚ]`, with `[K⁺ : ℚ] ≠ 0`, forces `[K : K⁺] = 2`.
    rintro ⟨hTC, hfin⟩
    have hb : Module.finrank (NumberField.maximalRealSubfield K) K = 2 := by
      have h1 : Module.finrank ℚ (NumberField.maximalRealSubfield K) *
          Module.finrank (NumberField.maximalRealSubfield K) K = Module.finrank ℚ K :=
        Module.finrank_mul_finrank ℚ _ K
      have hpos : 0 < Module.finrank ℚ (NumberField.maximalRealSubfield K) := by
        by_contra h
        rw [not_lt] at h
        have : Module.finrank ℚ K = 0 := by rw [← hfin, Nat.le_zero.mp h, mul_zero]
        exact absurd this (ne_of_gt Module.finrank_pos)
      refine Nat.mul_left_cancel hpos ?_
      rw [h1, ← hfin, mul_comm]
    exact { to_isTotallyComplex := hTC, is_quadratic := Algebra.IsQuadraticExtension.mk hb }

end Work.CMRealSubfield.RealSubfield

/-! The statement is also recorded under the (redundant) nested namespace used by the
delegation skeleton, so that consumers referring to the declaration by either name — in
particular both `Work.CMRealSubfield.RealSubfield.isCMField_iff_isTotallyComplex_and_finrank`
and its duplicate-namespace variant — find the same theorem. -/
namespace Work.CMRealSubfield.RealSubfield

namespace Work.CMRealSubfield.RealSubfield

theorem isCMField_iff_isTotallyComplex_and_finrank (K : Type*) [Field K] [NumberField K] :
    NumberField.IsCMField K ↔
      (NumberField.IsTotallyComplex K ∧
        2 * Module.finrank ℚ (NumberField.maximalRealSubfield K) = Module.finrank ℚ K) :=
  _root_.Work.CMRealSubfield.RealSubfield.isCMField_iff_isTotallyComplex_and_finrank K

end Work.CMRealSubfield.RealSubfield

end Work.CMRealSubfield.RealSubfield
