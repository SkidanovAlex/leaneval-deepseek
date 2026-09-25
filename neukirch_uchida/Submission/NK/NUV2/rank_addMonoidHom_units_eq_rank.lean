import Mathlib
import Submission.NK.NUV2.rank_addMonoidHom_padicInt

namespace NK.NUV2

/-- The `ℤ₂`-dual of the unit group of the ring of integers of a number field has rank equal to
the unit rank `r₁ + r₂ - 1` of `K`.

This is Dirichlet's unit theorem in the form `𝒪_Kˣ ≅ μ_K × ℤ^{rank K}` together with the
elementary fact that the dual of a torsion group into the torsion-free ring `ℤ₂` is trivial; the
unit group `Additive (𝒪_K)ˣ` is a finitely generated `ℤ`-module of `ℤ`-rank `rank K`
(`NumberField.Units.finrank_eq`), so `rank_addMonoidHom_padicInt` computes the dual. -/
theorem rank_addMonoidHom_units_eq_rank (K : Type) [Field K] [NumberField K] :
    Module.rank (PadicInt 2) (Additive ((NumberField.RingOfIntegers K)ˣ) →+ PadicInt 2)
      = (NumberField.Units.rank K : Cardinal) := by
  rw [rank_addMonoidHom_padicInt (p := 2) (Additive ((NumberField.RingOfIntegers K)ˣ))]
  rw [NumberField.Units.finrank_eq]

end NK.NUV2
