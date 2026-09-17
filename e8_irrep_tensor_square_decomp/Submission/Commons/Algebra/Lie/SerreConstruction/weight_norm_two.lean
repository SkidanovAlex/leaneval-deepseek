import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_root_weightSpace_finrank_eq_one
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_dominant_weight_eq_zero_or_theta
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_weightSpace_ascent
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_weightSpace_descent
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_weightSpace_eq_bot_of_not_root_again
import Submission.Commons.Algebra.Lie.e8_finrank
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_rootVector_card

namespace Commons.Algebra.Lie.SerreConstruction

/-- **Every nonzero weight of the adjoint representation of the Serre-constructed `e₈` is a root**:
its squared length for the Weyl-invariant form `μ ↦ μᵀA⁻¹μ` (`A = CartanMatrix.E₈`) is `2`.
Weights are stored in the `ω`-basis (`μ i` is the eigenvalue of `ad (SerreH i)`).

Proof route: a weight `μ` can be reflected into the dominant chamber by repeatedly applying the
"ascent" step `e8_weightSpace_ascent` (`μ ↦ μ + αᵢ` whenever `μ i ≤ -1`, which stays a weight);
the process terminates at a dominant weight, and by `e8_dominant_weight_eq_zero_or_theta` a nonzero
dominant weight is `θ`.  The squared length is preserved by each reflection (`qform_reflect` in
`Submission/Commons/Algebra/Lie/e8_finrank.lean`, together with `Qmu_eq_Qalpha_toAl`/`toAl_toMu` in
`e8_rootVector_card.lean`), and the squared length of `θ` is `2`. -/
theorem weight_norm_two {μ : Fin 8 → ℤ} (hμ : μ ≠ 0)
    (h : Commons.Algebra.Lie.SerreConstruction.wtSpace μ ≠ ⊥) :
    (∑ i, ∑ j, (μ i : ℚ) * ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j * (μ j : ℚ)) = 2 := by
  -- The commons lemma `e8_weightSpace_eq_bot_of_not_root_again` states precisely that a nonzero
  -- weight whose squared length is not `2` has trivial weight space; the claim is its contrapositive.
  by_contra hne
  exact h (e8_weightSpace_eq_bot_of_not_root_again μ hμ hne)

end Commons.Algebra.Lie.SerreConstruction
