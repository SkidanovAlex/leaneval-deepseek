import Mathlib
import Submission.NK.NUV2.rank_addMonoidHom_units_eq_rank

namespace NK.NUV2

/-- **The `ℤ₂`-dual of the unit group has rank at most the unit rank.**
Dirichlet's unit theorem says that `𝒪_Kˣ ≅ μ_K × ℤ^{r₁ + r₂ - 1}`; since `ℤ₂ = PadicInt 2` is
torsion free, the dual of the finite torsion part `μ_K` is trivial, while
`Hom(ℤ^{r}, ℤ₂) ≅ ℤ₂^{r}` has `ℤ₂`-rank `r`.  Hence the `ℤ₂`-rank of the (unrestricted) additive
dual `Hom(𝒪_Kˣ, ℤ₂)` is exactly the unit rank `r₁ + r₂ - 1`, so in particular it is at most
that number.  This is the `≤` form used downstream. -/
theorem rank_unitsDual_le (K : Type) [Field K] [NumberField K] :
    Module.rank (PadicInt 2) (Additive ((NumberField.RingOfIntegers K)ˣ) →+ PadicInt 2)
      ≤ ((NumberField.InfinitePlace.nrRealPlaces K
            + NumberField.InfinitePlace.nrComplexPlaces K - 1 : ℕ) : Cardinal) := by
  have hrank : NumberField.Units.rank K
      = NumberField.InfinitePlace.nrRealPlaces K
        + NumberField.InfinitePlace.nrComplexPlaces K - 1 := by
    rw [NumberField.Units.rank,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  rw [rank_addMonoidHom_units_eq_rank]
  exact Nat.cast_le.mpr (le_of_eq hrank)

end NK.NUV2
