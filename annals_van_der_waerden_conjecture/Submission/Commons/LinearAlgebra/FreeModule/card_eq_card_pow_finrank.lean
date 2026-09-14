import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

namespace Commons.LinearAlgebra.FreeModule

/-- If `M` is a finite free module over the finite ring `R`, then the cardinality of `M`
is the cardinality of `R` raised to the `R`-finrank of `M`. -/
theorem card_eq_card_pow_finrank {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [Finite R] [Finite M] :
    Nat.card M = Nat.card R ^ Module.finrank R M := by
  by_cases hR : Nontrivial R
  · have : StrongRankCondition R := commRing_strongRankCondition R
    let ι := Module.Free.ChooseBasisIndex R M
    calc
      Nat.card M = Nat.card (ι →₀ R) := by
        exact Nat.card_congr (Module.Free.chooseBasis R M).repr.toEquiv
      _ = Nat.card (ι → R) := by
        exact Nat.card_congr (Finsupp.equivFunOnFinite (M := R))
      _ = Nat.card R ^ Nat.card ι := by
        exact Nat.card_fun (α := ι) (β := R)
      _ = Nat.card R ^ Module.finrank R M := by
        rw [Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis R M)]
  · have : Subsingleton R := (not_nontrivial_iff_subsingleton.mp hR)
    have : Subsingleton M := Module.subsingleton R M
    calc
      Nat.card M = 1 := Nat.card_of_subsingleton (0 : M)
      _ = Nat.card R ^ Module.finrank R M := by
        rw [Nat.card_of_subsingleton (0 : R)]
        rw [one_pow]

end Commons.LinearAlgebra.FreeModule