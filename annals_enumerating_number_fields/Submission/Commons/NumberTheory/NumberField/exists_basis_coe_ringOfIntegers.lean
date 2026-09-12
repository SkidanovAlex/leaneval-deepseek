import Mathlib.NumberTheory.NumberField.Basic

namespace Commons.NumberTheory.NumberField

/-- Given a `ℤ`-basis `ωb` of the ring of integers `𝓞 K` of a number field `K` of degree `n`, the
images of `ωb` in `K` form a `ℚ`-basis of `K`. -/
theorem exists_basis_coe_ringOfIntegers (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (ωb : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K)) (hn : Module.finrank ℚ K = n) :
    ∃ b : Module.Basis (Fin n) ℚ K, ∀ k, b k = ((ωb k : NumberField.RingOfIntegers K) : K) := by
  have _ := hn
  exact ⟨Module.Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) K ωb, fun k => by
    rw [Module.Basis.localizationLocalization_apply]⟩

end Commons.NumberTheory.NumberField