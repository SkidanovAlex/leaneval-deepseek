import Submission.Work.AggregateBoundary
import Submission.Work.SystemReducedImage

open FreeGroup
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# The aggregate step: a long image gives a strict move or a Fall-II state

The first link of the reduction protocol (`ImageAggregate` +
`SystemReducedImage` + `AggregateBoundary`):

* if some basis image is genuinely long (`∃ i, 1 < |α(aᵢ)|`), a standard
  generator `a_m` has an aggregate expression with a *confined* factor
  (`exists_confined_image_aggregate`);
* a confined factor in *any* position of an image aggregate of length ≥ 2 is
  either strictly shortening (`∃ γ ∈ AutClosure n, N (α·γ) < N α` — boundary
  factors, and interior factors whose strict phase fires) or an *interior*
  balanced (Fall II) factor (`confined_factor_reduces`).

So, assembled, **every automorphism with a long image** either admits a single
closure move strictly decreasing the total length `N`, or exhibits a Fall-II
configuration: an interior confined factor `j` of the aggregate of some
`a_m` whose word splits `es[j] = A ++ B` (`|A| = |B|`) with the two
neighbours covering the two halves — the input of the T3 rebalancing phase.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- **The aggregate step (Fall I / Fall II).**  For every automorphism `α`
with a long basis image, either a single elementary closure move strictly
decreases the total length (`N (α·γ) < N α`), or the *balanced* (Fall II)
configuration of an aggregate is exhibited: an interior confined factor `j`
of the image aggregate of a standard generator `a_m` with word
`A ++ B` (`|A| = |B|`), the left neighbour's word `X ++ invRev A`, the right
neighbour's word `invRev B ++ Z`. -/
theorem aggregate_reduces_or_balanced {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hlong : ∃ i : Fin n, 1 < FreeGroup.norm (α (FreeGroup.of i))) :
    (∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α) ∨
    (∃ (m : Fin n) (j : ℕ) (hj : j < (imageAggregate α m).length)
        (hj0 : 0 < j) (hj1 : j + 1 < (imageAggregate α m).length),
      Confined (aggregateWords (imageAggregate α m)) j ∧
      ∃ (A B X Z : List (Fin n × Bool)),
        ((imageAggregate α m)[j]).toWord = A ++ B ∧ A.length = B.length ∧
        ((imageAggregate α m)[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
        ((imageAggregate α m)[j + 1]).toWord = FreeGroup.invRev B ++ Z) := by
  classical
  -- a standard generator `a_m` whose aggregate has ≥ 2 factors
  rcases exists_two_factor_letter α hlong with ⟨m, hlen⟩
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have hk : 2 ≤ es.length := by
    dsimp [es]
    rw [imageAggregate_length]
    exact hlen
  have hprod : es.prod = FreeGroup.of m := by
    dsimp [es]
    exact imageAggregate_prod_letter α m
  rcases aggregate_confined_factor es m hprod hk with ⟨j, hj, hconf⟩
  have himg : ImageAggregate α es := by
    dsimp [es]
    exact imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    dsimp [es]
    exact SystemReduced_imageAggregate α m
  rcases confined_factor_reduces α es himg hred hk hj hconf with hs | hbal
  · left
    exact hs
  · right
    rcases hbal with ⟨hj0, hj1, hm, A, B, X, Z, hA, hAB, hX, hZ⟩
    exact ⟨m, j, (by simpa [es] using hj), hj0, hj1, (by simpa [es] using hconf),
      A, B, X, Z, (by simpa [es] using hA), hAB,
      (by simpa [es] using hX), (by simpa [es] using hZ)⟩

end Submission.Nielsen
