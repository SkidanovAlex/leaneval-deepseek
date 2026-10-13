import Mathlib
import Submission.Work.DSEQP.Basic

/-!
# Almost zero is detected after a faithfully flat base change

If `R → S` is a faithfully flat algebra and the base change `S ⊗[R] M` of an
`R`-module `M` is almost zero with respect to the sequence `t : ℕ → R` (regarded
in `S` via `algebraMap`), then `M` itself is almost zero with respect to `t`.

The proof is the injectivity of the natural map `M →ₗ[R] S ⊗[R] M`, `m ↦ 1 ⊗ₜ[R] m`,
for a faithfully flat `R`-algebra `S` (Mathlib's
`Module.FaithfullyFlat.tensorProduct_mk_injective`). That map is `R`-linear, so it
carries `t e • m` to `t e • (1 ⊗ₜ[R] m)`, and the `R`-action on `S ⊗[R] M` agrees
with the `S`-action of `algebraMap R S (t e)`, which is zero by hypothesis.
-/

open scoped TensorProduct

namespace Work.DSEQP

/-- The canonical map `M →ₗ[R] S ⊗[R] M`, `m ↦ 1 ⊗ₜ[R] m`, is injective for a
faithfully flat `R`-algebra `S`. -/
theorem tensorProduct_mk_one_injective {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective (TensorProduct.mk R S M 1) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) M

/-- The `R`-action on `S ⊗[R] M` is the restriction of the `S`-action along
`algebraMap R S`: on the element `1 ⊗ₜ[R] m` the two actions of `r : R` coincide. -/
theorem smul_one_tmul {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (r : R) (m : M) :
    r • ((1 : S) ⊗ₜ[R] m) = algebraMap R S r • ((1 : S) ⊗ₜ[R] m) := by
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]

/-- Almost vanishing is detected after a faithfully flat base change: if `S ⊗[R] M` is
killed by every `algebraMap R S (t e)` then `M` is killed by every `t e`. -/
theorem almostZero_of_faithfullyFlat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (t : ℕ → R) (M : Type*) [AddCommGroup M] [Module R M]
    (h : AlmostZero (fun e => algebraMap R S (t e)) (TensorProduct R S M)) : AlmostZero t M := by
  intro e m
  refine tensorProduct_mk_one_injective (R := R) (S := S) M ?_
  rw [map_smul, map_zero, TensorProduct.mk_apply, smul_one_tmul]
  exact h e _

end Work.DSEQP
