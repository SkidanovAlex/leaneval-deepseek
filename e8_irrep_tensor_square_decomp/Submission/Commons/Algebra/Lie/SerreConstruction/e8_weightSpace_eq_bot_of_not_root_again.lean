/-
# Weight spaces of the Serre-constructed `e₈` outside the roots

The weight space of the adjoint representation of `e₈ = LieAlgebra.e₈ ℂ` at an integral weight
`μ` is `wtSpace μ = ⨅ i, ker (ad (H i) - μ i)`; it is nonzero exactly for `μ = 0` and for the
`240` roots, i.e. exactly for the integral weights `μ` with squared length `2` for the
Weyl-invariant form `(μ,μ) = μᵀ A⁻¹ μ` (`A = CartanMatrix.E₈`).

The main theorem below is the "support" half of the root space decomposition of the
Serre-constructed `e₈`.  Its proof rests on the following ingredients, developed in the shared
commons (several of them requested from the fleet while this file was being written):

* the triangular decomposition `e₈ = 𝔥 ⊕ 𝔫⁺ ⊕ 𝔫⁻` and the fact that every weight vector
  lies in one of the two root cones (`e8_W_eq_bot_of_not_cone`);
* **the descent lemma** (`e8_weightSpace_descent`): if `ν` is a weight with `ν i ≥ 1` then
  `ν - α i` is again a weight, proved from the Serre relations via local nilpotency of `ad (E i)`
  and the `sl₂`-string lemma `string_of_locallyNilpotent`; and dually the **ascent lemma**
  (`e8_weightSpace_ascent`);
* the classification of the dominant weights (`e8_dominant_weight_eq_zero_or_theta`: they are
  `0` and the highest root `θ = ω₈`) via the height induction along the descents;
* the reflection machinery (`e8_weightSpace_reflect_ne_bot`, `wtReflect`,
  `e8_weightSpace_exists_dominant_reflect`) reducing an arbitrary nonzero weight to a dominant
  one;
* the root space dimensions (`e8_root_weightSpace_finrank_eq_one`) and the root count
  (`exists_finset_e8_roots`, `e8_rootVector_card`).

The theorem `e8W_eq_bot_of_not_root` in the commons (`Submission.Commons.Algebra.Lie.e8_finrank`)
is the assembled result, and the statement below is its public form in the
`SerreConstruction` namespace, with the weight space written out as an intersection of kernels.
-/
import Mathlib
import Submission.Commons.Algebra.Lie.e8_finrank

set_option linter.unusedVariables false

noncomputable section
open CartanMatrix

namespace Commons.Algebra.Lie.SerreConstruction

/-- **The weight spaces of the Serre-constructed `e₈` outside the `240` roots are trivial.**

For an integral weight `μ ≠ 0` whose squared length `μᵀA⁻¹μ` is not `2` (equivalently: `μ` is not
one of the `240` roots of `E₈`), the joint kernel of the eight operators `ad (H i) - μ i` is zero. -/
theorem e8_weightSpace_eq_bot_of_not_root_again (μ : Fin 8 → ℤ) (hμ : μ ≠ 0)
    (h : (∑ i, ∑ j, (μ i : ℚ) * ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j * (μ j : ℚ))
      ≠ 2) :
    (⨅ i : Fin 8, LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)
      (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))) - (μ i : ℂ) • 1)) = ⊥ :=
  Commons.Algebra.Lie.e8W_eq_bot_of_not_root μ hμ h

end Commons.Algebra.Lie.SerreConstruction
