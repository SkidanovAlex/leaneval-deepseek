import Mathlib
import Submission.Work.ORFP2.Basic
import Submission.Work.ORFP2.augIdeal_eq_span_of_surjective

namespace Work.ORFP2

open MonoidAlgebra

/-- For a free group `F(α)` and a commutative ring `k`, the `k[F(α)]`-linear map
`c ↦ ∑_a c a * (x_a - 1)` from `α →₀ k[F(α)]` to `k[F(α)]` is **surjective** onto the
augmentation ideal `augIdeal k (F(α))`.

The range of `Finsupp.linearCombination` is the `k[F(α)]`-span of the vectors `x_a - 1`; since the
generators `of a` generate `F(α)`, that span is exactly the augmentation ideal, as recorded in
`Work.ORFP2.augIdeal_eq_span_of_surjective`. -/
theorem augIdeal_freeGroup_surjective (k : Type*) [CommRing k] (α : Type*) [DecidableEq α] :
    LinearMap.range (Finsupp.linearCombination (MonoidAlgebra k (FreeGroup α))
        (fun a : α => MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)) =
      augIdeal k (FreeGroup α) := by
  rw [Finsupp.range_linearCombination, augIdeal_eq_span_of_surjective k (FreeGroup α) α
      (MonoidHom.id (FreeGroup α)) Function.surjective_id]
  rfl

end Work.ORFP2
