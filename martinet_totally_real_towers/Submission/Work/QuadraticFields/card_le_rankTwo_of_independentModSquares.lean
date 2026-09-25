import Mathlib
import Submission.Work.QuadraticFields.RankTwo

namespace Work.QuadraticFields

/-- A family independent modulo squares spans an `𝔽₂`-subspace of `A ⧸ A²` of dimension equal to
its cardinality, whence the cardinality is at most the `2`-rank of `A`. -/
theorem card_le_rankTwo_of_independentModSquares {A : Type*} [CommGroup A]
    [Module.Finite (ZMod 2) (ModN (Additive A) 2)] {ι : Type*} [Fintype ι]
    (a : ι → A) (h : IndependentModSquares a) : Fintype.card ι ≤ rankTwo A :=
  LinearIndependent.fintype_card_le_finrank h

end Work.QuadraticFields
