import Mathlib
import Submission.Work.DSG4b.LCF.Basic

/-!
# `M ⊗[R] I` is a finite `S`-module when `M` is finite over `S` and `I` is finitely generated

Let `R → S` be a ring homomorphism (so that `S` is an `R`-algebra), let `M` be an `S`-module
which is finite over `S`, and let `I ⊆ R` be a finitely generated ideal.  Then `M ⊗[R] I`,
which is an `S`-module by acting on the factor `M`, is finite over `S`.

The proof writes `M ⊗[R] I ≃ₗ[S] M ⊗[S] (S ⊗[R] I)` (`TensorProduct.AlgebraTensorModule.cancelBaseChange`):
the second factor `S ⊗[R] I` is finite over `S` by base change along `R → S`
(`Module.Finite.base_change`), hence so is the tensor product over `S` of it with the finite
`S`-module `M` (`Module.Finite.tensorProduct`).

This is the finiteness input needed when applying Nakayama-type arguments to `M ⊗[R] I`
in the local criterion of flatness.
-/

namespace Work.DSG4b.LCF

theorem module_finite_tensor_of_fg {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (I : Ideal R) (hI : I.FG) : Module.Finite S (TensorProduct R M I) := by
  -- `I`, viewed as an `R`-module, is finitely generated.
  have hIfin : Module.Finite R (I : Type _) := Module.Finite.of_fg hI
  -- Base change: `S ⊗[R] I` is a finite `S`-module.
  have hbase : Module.Finite S (TensorProduct R S I) := inferInstance
  -- Hence `M ⊗[S] (S ⊗[R] I)` is a finite `S`-module, since `M` is finite over `S`.
  have hprod : Module.Finite S (TensorProduct S M (TensorProduct R S I)) := inferInstance
  -- `M ⊗[S] (S ⊗[R] I) ≃ₗ[S] M ⊗[R] I`, so the latter is finite too.
  have e := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M I
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

end Work.DSG4b.LCF
