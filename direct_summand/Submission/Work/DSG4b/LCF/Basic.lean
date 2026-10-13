import Mathlib

/-!
# Auxiliary lemmas for the local criterion of flatness

This file collects the elementary `TensorProduct` bookkeeping used in the proof of the local
criterion of flatness (Stacks 00MK), see `Submission/Work/DSG4b/localCriterionOfFlatness.lean`.

The main contents are

* `LCF.injective_lTensor_of_comp_rid` / `LCF.injective_comp_rid_of_lTensor`: composing a map
  `LinearMap.lTensor R M f : M ⊗ N → M ⊗ R` with the isomorphism `TensorProduct.rid R M`
  does not change injectivity;
* `LCF.prodRight_lTensor_fst_snd`: the component-wise description of `TensorProduct.prodRight`
  applied to `LinearMap.lTensor M f`.
-/

namespace Work.DSG4b.LCF

open TensorProduct LinearMap

section rid

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- Composing `LinearMap.lTensor M f : M ⊗ N → M ⊗ R` with the isomorphism `M ⊗ R ≃ M` does not
change injectivity. -/
lemma injective_lTensor_of_comp_rid (f : N →ₗ[R] R) :
    Function.Injective ((TensorProduct.rid R M).toLinearMap ∘ₗ LinearMap.lTensor M f) ↔
      Function.Injective (LinearMap.lTensor M f) := by
  simpa [LinearMap.coe_comp] using
    Function.Injective.of_comp_iff (TensorProduct.rid R M).injective (⇑(LinearMap.lTensor M f))

end rid

section prod

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

open TensorProduct in
/-- `TensorProduct.prodRight` applied to `LinearMap.lTensor M f` for a map
`f : N →ₗ[R] P × Q` splits into the two components. -/
lemma prodRight_lTensor_fst_snd {N P Q : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] [AddCommGroup Q] [Module R Q] (f : N →ₗ[R] P × Q) (z : M ⊗[R] N) :
    TensorProduct.prodRight R R M P Q (LinearMap.lTensor M f z) =
      (LinearMap.lTensor M (LinearMap.fst R P Q ∘ₗ f) z,
        LinearMap.lTensor M (LinearMap.snd R P Q ∘ₗ f) z) := by
  induction z using TensorProduct.induction_on with
  | zero => ext <;> simp
  | tmul m n => simp
  | add x y hx hy => simp [map_add, hx, hy]

end prod

end Work.DSG4b.LCF
