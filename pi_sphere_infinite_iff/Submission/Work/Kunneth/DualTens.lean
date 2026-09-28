import Mathlib
import Submission.Work.Kunneth.TensorCo
import Submission.Work.Kunneth.Tensor
import Submission.Work.Kunneth.Algebra
import Submission.Work.Kunneth.ctensAux

/-!
# Dualising a tensor product with a finite free module

`Work.Kunneth.dualDistribEquivRight A N` is the equivalence

`(A ⊗_ℤ N →ₗ ℤ) ≃ₗ (A →ₗ ℤ) ⊗_ℤ (N →ₗ ℤ)`

valid for an *arbitrary* `ℤ`-module `A` and a finite free `ℤ`-module `N`.  It is the composite of
the hom-tensor adjunction `(A ⊗ N →ₗ ℤ) ≃ (A →ₗ N →ₗ ℤ)` with the inverse of the contraction
`dualTensorHom : (A →ₗ ℤ) ⊗ (N →ₗ ℤ) → (A →ₗ N →ₗ ℤ)`, the latter being an isomorphism because
`N →ₗ ℤ` is finite projective.

The properties recorded here are

* `dualDistrib_dualDistribEquivRight` — `e` is a right inverse of `TensorProduct.dualDistrib`
  (the evaluation of a pair of functionals on a pair of vectors);
* `dualDistribEquivRight_dualDistrib` — and a left inverse;
* `dualDistrib_injective` — consequently `TensorProduct.dualDistrib` is injective;
* `dualDistribEquivRight_natural` — naturality in the *first* variable, which is what makes the
  identification of the differentials in `Work.Kunneth.ctens_dual_tpC` work.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

section ModuleLevel

variable (A N : Type*) [AddCommGroup A] [Module ℤ A] [AddCommGroup N] [Module ℤ N]

/-- The contraction `(A →ₗ ℤ) ⊗ (N →ₗ ℤ) →ₗ (A →ₗ N →ₗ ℤ)` is an isomorphism when `N` is
finite free: the source is exactly `(A →ₗ ℤ)^{rk N} ≅ (A →ₗ N →ₗ ℤ)`. -/
def dualTensorHomDualEquiv [Module.Finite ℤ N] [Module.Free ℤ N] :
    ((A →ₗ[ℤ] ℤ) ⊗[ℤ] (N →ₗ[ℤ] ℤ)) ≃ₗ[ℤ] (A →ₗ[ℤ] N →ₗ[ℤ] ℤ) :=
  LinearEquiv.ofBijective (dualTensorHom ℤ A (N →ₗ[ℤ] ℤ))
    dualTensorHom_bijective_of_finite_projective_right

/-- **The dual of a tensor product with a finite free module.** -/
def dualDistribEquivRight [Module.Finite ℤ N] [Module.Free ℤ N] :
    (A ⊗[ℤ] N →ₗ[ℤ] ℤ) ≃ₗ[ℤ] (A →ₗ[ℤ] ℤ) ⊗[ℤ] (N →ₗ[ℤ] ℤ) :=
  (TensorProduct.lift.equiv (RingHom.id ℤ) A N ℤ).symm.trans (dualTensorHomDualEquiv A N).symm

/-- The value of `dualDistribEquivRight` in terms of the hom-tensor adjunction. -/
theorem dualTensorHom_dualDistribEquivRight [Module.Finite ℤ N] [Module.Free ℤ N]
    (f : A ⊗[ℤ] N →ₗ[ℤ] ℤ) :
    dualTensorHom ℤ A (N →ₗ[ℤ] ℤ) (dualDistribEquivRight A N f)
      = (TensorProduct.lift.equiv (RingHom.id ℤ) A N ℤ).symm f := by
  rw [dualDistribEquivRight, LinearEquiv.trans_apply]
  exact LinearEquiv.apply_symm_apply (dualTensorHomDualEquiv A N) _

/-- The value of a pair of functionals on a pair of vectors, transported to `A →ₗ N →ₗ ℤ`. -/
theorem dualTensorHom_apply_eq_dualDistrib (y : (A →ₗ[ℤ] ℤ) ⊗[ℤ] (N →ₗ[ℤ] ℤ)) (a : A) (n : N) :
    ((dualTensorHom ℤ A (N →ₗ[ℤ] ℤ)) y a) n = TensorProduct.dualDistrib ℤ A N y (a ⊗ₜ[ℤ] n) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul f g => simp [TensorProduct.dualDistrib_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- `dualDistribEquivRight` is a right inverse of the pairing `TensorProduct.dualDistrib`. -/
theorem dualDistrib_dualDistribEquivRight [Module.Finite ℤ N] [Module.Free ℤ N]
    (f : A ⊗[ℤ] N →ₗ[ℤ] ℤ) :
    TensorProduct.dualDistrib ℤ A N (dualDistribEquivRight A N f) = f := by
  ext a n
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  rw [← dualTensorHom_apply_eq_dualDistrib A N (dualDistribEquivRight A N f) a n,
    dualTensorHom_dualDistribEquivRight, TensorProduct.lift.equiv_symm_apply]

/-- `dualDistribEquivRight` is a left inverse of the pairing `TensorProduct.dualDistrib`. -/
theorem dualDistribEquivRight_dualDistrib [Module.Finite ℤ N] [Module.Free ℤ N]
    (y : (A →ₗ[ℤ] ℤ) ⊗[ℤ] (N →ₗ[ℤ] ℤ)) :
    dualDistribEquivRight A N (TensorProduct.dualDistrib ℤ A N y) = y := by
  apply (dualTensorHomDualEquiv A N).injective
  rw [dualTensorHomDualEquiv, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply,
    dualTensorHom_dualDistribEquivRight]
  ext a n
  rw [TensorProduct.lift.equiv_symm_apply, dualTensorHom_apply_eq_dualDistrib]

/-- Two elements of `(A →ₗ ℤ) ⊗ (N →ₗ ℤ)` are equal as soon as their pairings with pure tensors
agree, `N` being finite free. -/
theorem dualDistrib_injective [Module.Finite ℤ N] [Module.Free ℤ N]
    {x y : (A →ₗ[ℤ] ℤ) ⊗[ℤ] (N →ₗ[ℤ] ℤ)}
    (h : TensorProduct.dualDistrib ℤ A N x = TensorProduct.dualDistrib ℤ A N y) : x = y := by
  rw [← dualDistribEquivRight_dualDistrib A N x, ← dualDistribEquivRight_dualDistrib A N y, h]

/-- Naturality of the pairing in the first variable: transporting a functional along `d` in the
first tensor factor is the same as applying the transpose of `d` to the second pairing. -/
theorem dualDistrib_natural {A' : Type*} [AddCommGroup A'] [Module ℤ A']
    (d : A →ₗ[ℤ] A') (y : (A' →ₗ[ℤ] ℤ) ⊗[ℤ] (N →ₗ[ℤ] ℤ)) (a : A) (n : N) :
    TensorProduct.dualDistrib ℤ A N (LinearMap.rTensor (N →ₗ[ℤ] ℤ) d.dualMap y) (a ⊗ₜ[ℤ] n)
      = TensorProduct.dualDistrib ℤ A' N y (d a ⊗ₜ[ℤ] n) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul f g => simp [TensorProduct.dualDistrib_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- **Naturality of `dualDistribEquivRight` in the first variable.** -/
theorem dualDistribEquivRight_natural [Module.Finite ℤ N] [Module.Free ℤ N]
    {A' : Type*} [AddCommGroup A'] [Module ℤ A']
    (d : A →ₗ[ℤ] A') (u : A' ⊗[ℤ] N →ₗ[ℤ] ℤ) :
    dualDistribEquivRight A N (u.comp (LinearMap.rTensor N d))
      = LinearMap.rTensor (N →ₗ[ℤ] ℤ) d.dualMap (dualDistribEquivRight A' N u) := by
  apply dualDistrib_injective A N
  ext a n
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  rw [dualDistrib_dualDistribEquivRight A N (u.comp (LinearMap.rTensor N d)),
    dualDistrib_natural A N d (dualDistribEquivRight A' N u) a n,
    dualDistrib_dualDistribEquivRight A' N u,
    LinearMap.comp_apply, LinearMap.rTensor_tmul]

end ModuleLevel

/-- **`Hom` out of a finite direct sum is the product of the `Hom`s.** -/
def homDirectSumEquivPi (R : Type*) [CommSemiring R] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (X : ι → Type*) [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]
    (P : Type*) [AddCommMonoid P] [Module R P] :
    ((DirectSum ι X) →ₗ[R] P) ≃ₗ[R] (∀ i, X i →ₗ[R] P) :=
  LinearEquiv.ofLinearMap
    (LinearMap.pi (fun i => (DirectSum.lof R ι X i).lcomp R P))
    { toFun := fun ψ => DirectSum.toModule R ι P ψ
      map_add' := by
        intro ψ ψ'
        apply DirectSum.linearMap_ext R
        intro i
        apply LinearMap.ext
        intro x
        simp [DirectSum.toModule_lof, Pi.add_apply]
      map_smul' := by
        intro c ψ
        apply DirectSum.linearMap_ext R
        intro i
        apply LinearMap.ext
        intro x
        simp [DirectSum.toModule_lof, Pi.smul_apply] }
    (by
      apply LinearMap.ext
      intro ψ
      funext i
      apply LinearMap.ext
      intro x
      simp [LinearMap.pi_apply, LinearMap.lcomp_apply, DirectSum.toModule_lof])
    (by
      apply LinearMap.ext
      intro φ
      apply DirectSum.linearMap_ext R
      intro i
      apply LinearMap.ext
      intro x
      simp [LinearMap.pi_apply, LinearMap.lcomp_apply, DirectSum.toModule_lof])

@[simp]
theorem homDirectSumEquivPi_apply (R : Type*) [CommSemiring R] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (X : ι → Type*) [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]
    (P : Type*) [AddCommMonoid P] [Module R P]
    (φ : (DirectSum ι X) →ₗ[R] P) (i : ι) :
    homDirectSumEquivPi R ι X P φ i = φ.comp (DirectSum.lof R ι X i) := by
  show (LinearMap.pi (fun i => (DirectSum.lof R ι X i).lcomp R P)) φ i
    = φ.comp (DirectSum.lof R ι X i)
  rw [LinearMap.pi_apply]
  rfl

@[simp]
theorem homDirectSumEquivPi_symm_apply (R : Type*) [CommSemiring R] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (X : ι → Type*) [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]
    (P : Type*) [AddCommMonoid P] [Module R P]
    (ψ : ∀ i, X i →ₗ[R] P) :
    (homDirectSumEquivPi R ι X P).symm ψ = DirectSum.toModule R ι P ψ := rfl


end

end Work.Kunneth
