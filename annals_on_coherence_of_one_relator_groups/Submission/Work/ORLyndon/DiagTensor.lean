import Mathlib
import Submission.Work.ORLyndon.ProjDim

/-!
# The diagonal action of a group algebra on a tensor product

For a field `K`, a group `G` and two left `K[G]`-modules `N`, `M`, the tensor product
`N ⊗[K] M` carries the *diagonal* `K[G]`-module structure
`g • (n ⊗ₜ m) = (g • n) ⊗ₜ (g • m)`.

This structure is the key ingredient in showing that a projective resolution of the trivial
`K[G]`-module of length `n` yields a projective resolution of length `n` of *every* `K[G]`-module
(the resolution terms have to be tensored with `M` over `K`).

Mathlib defines a competing "left" action (`a • (n ⊗ₜ m) = (a • n) ⊗ₜ m`), which is *not* the
one we need; we remove those instances locally and replace them by the diagonal action.
-/

set_option autoImplicit false

open TensorProduct

namespace Work.ORLyndon

attribute [-instance] TensorProduct.leftModule TensorProduct.leftDistribMulAction
  TensorProduct.leftHasSMul

universe u

variable {K : Type*} [Field K] {G : Type*} [Group G]

section Core

variable {N M : Type*} [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N]
  [IsScalarTower K (MonoidAlgebra K G) N]
  [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
  [IsScalarTower K (MonoidAlgebra K G) M]

/-- The linear map `v ↦ single g 1 • v` is compatible with multiplication in the group. -/
theorem groupSMulLinearMap_mul (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V] (x y : G) :
    MonoidAlgebra.GroupSMul.linearMap K V (x * y) =
      MonoidAlgebra.GroupSMul.linearMap K V x * MonoidAlgebra.GroupSMul.linearMap K V y := by
  ext n
  simp only [MonoidAlgebra.GroupSMul.linearMap_apply, Module.End.mul_apply]
  rw [← mul_smul, MonoidAlgebra.single_mul_single, mul_one]

/-- The linear map `v ↦ single g 1 • v` for `g = 1` is the identity. -/
theorem groupSMulLinearMap_one (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V] :
    MonoidAlgebra.GroupSMul.linearMap K V (1 : G) = 1 := by
  ext n
  rw [MonoidAlgebra.GroupSMul.linearMap_apply, ← MonoidAlgebra.one_def, one_smul]
  rfl

/-- The monoid hom `G →* End_K (N ⊗[K] M)` giving the diagonal action. -/
noncomputable def diagMonoidHom : G →* Module.End K (N ⊗[K] M) where
  toFun g := TensorProduct.map (MonoidAlgebra.GroupSMul.linearMap K N g)
    (MonoidAlgebra.GroupSMul.linearMap K M g)
  map_one' := by
    rw [groupSMulLinearMap_one N, groupSMulLinearMap_one M]
    simp only [Module.End.one_eq_id, map_id]
  map_mul' := by
    intro x y
    rw [groupSMulLinearMap_mul N, groupSMulLinearMap_mul M]
    simp only [Module.End.mul_eq_comp, map_comp]

/-- The algebra hom `K[G] →ₐ[K] End_K (N ⊗[K] M)` giving the diagonal action. -/
noncomputable def diagAlgHom :
    MonoidAlgebra K G →ₐ[K] Module.End K (N ⊗[K] M) :=
  MonoidAlgebra.lift K (Module.End K (N ⊗[K] M)) G (diagMonoidHom (N := N) (M := M))

/-- The diagonal `K[G]`-module structure on `N ⊗[K] M`. -/
noncomputable instance diagModule : Module (MonoidAlgebra K G) (N ⊗[K] M) :=
  Module.compHom (N ⊗[K] M) (diagAlgHom (N := N) (M := M)).toRingHom

theorem diagModule_apply (a : MonoidAlgebra K G) (x : N ⊗[K] M) :
    a • x = diagAlgHom (N := N) (M := M) a x := rfl

/-- The diagonal action of a single group element on a pure tensor. -/
theorem diagModule_single_tmul (g : G) (n : N) (m : M) :
    MonoidAlgebra.single g (1 : K) • (n ⊗ₜ[K] m) =
      (MonoidAlgebra.single g (1 : K) • n) ⊗ₜ[K] (MonoidAlgebra.single g (1 : K) • m) := by
  rw [diagModule_apply, diagAlgHom, MonoidAlgebra.lift_single]
  simp only [diagMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk, map_tmul,
    MonoidAlgebra.GroupSMul.linearMap_apply, one_smul]

/-- The diagonal action of a group element on a pure tensor. -/
theorem diagModule_of_tmul (g : G) (n : N) (m : M) :
    (MonoidAlgebra.of K G g) • (n ⊗ₜ[K] m) =
      (MonoidAlgebra.of K G g • n) ⊗ₜ[K] (MonoidAlgebra.of K G g • m) :=
  diagModule_single_tmul g n m

end Core

section Map

variable {N M : Type*} [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N]
  [IsScalarTower K (MonoidAlgebra K G) N]
  [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
  [IsScalarTower K (MonoidAlgebra K G) M]
variable {N' : Type*} [AddCommGroup N'] [Module K N'] [Module (MonoidAlgebra K G) N']
  [IsScalarTower K (MonoidAlgebra K G) N']

/-- The diagonal action is compatible with the `K`-scalar structure. -/
instance diagIsScalarTower : IsScalarTower K (MonoidAlgebra K G) (N ⊗[K] M) where
  smul_assoc k a x := by
    rw [diagModule_apply, diagModule_apply, Algebra.smul_def, map_mul, AlgHom.commutes,
      Module.End.mul_apply, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply]

/-- The `K`-linear map underlying a `K[G]`-linear map. -/
noncomputable def kLinear (f : N →ₗ[MonoidAlgebra K G] N') : N →ₗ[K] N' :=
  f.restrictScalars K

theorem kLinear_apply (f : N →ₗ[MonoidAlgebra K G] N') (n : N) : kLinear f n = f n := rfl

/-- Tensoring a `K[G]`-linear map with the identity of `M` is `K[G]`-linear for the diagonal
action. -/
noncomputable def diagTensorMap (f : N →ₗ[MonoidAlgebra K G] N') :
    N ⊗[K] M →ₗ[MonoidAlgebra K G] N' ⊗[K] M :=
  MonoidAlgebra.equivariantOfLinearOfComm
    (TensorProduct.map (kLinear f) (LinearMap.id : M →ₗ[K] M)) (by
      intro g x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [smul_add, map_add, ha, hb]
      | tmul n m =>
        simp only [diagModule_single_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
          kLinear_apply, map_smul])

theorem diagTensorMap_tmul (f : N →ₗ[MonoidAlgebra K G] N') (n : N) (m : M) :
    diagTensorMap f (n ⊗ₜ[K] m) = f n ⊗ₜ[K] m := by
  simp only [diagTensorMap, MonoidAlgebra.equivariantOfLinearOfComm_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, kLinear_apply]

end Map



section Surj

variable {N M : Type*} [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N]
  [IsScalarTower K (MonoidAlgebra K G) N]
  [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
  [IsScalarTower K (MonoidAlgebra K G) M]
variable {N' : Type*} [AddCommGroup N'] [Module K N'] [Module (MonoidAlgebra K G) N']
  [IsScalarTower K (MonoidAlgebra K G) N']

theorem diagTensorMap_surjective {f : N →ₗ[MonoidAlgebra K G] N'}
    (hf : Function.Surjective f) : Function.Surjective (diagTensorMap (M := M) f) := by
  rw [← LinearMap.range_eq_top]
  rw [eq_top_iff]
  rintro y -
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | tmul n' m =>
      obtain ⟨n, rfl⟩ := hf n'
      exact ⟨n ⊗ₜ[K] m, by rw [diagTensorMap_tmul]⟩

end Surj


end Work.ORLyndon
