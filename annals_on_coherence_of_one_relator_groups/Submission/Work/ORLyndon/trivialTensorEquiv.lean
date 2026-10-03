import Mathlib
import Submission.Work.ORLyndon.DiagTensor
import Submission.Work.ORLyndon.Augmentation
import Submission.Work.ORLyndon.AugQuot
import Submission.Work.ORLyndon.augQuot_smul
import Submission.Work.ORLyndon.augQuot_smul_one

/-!
# The trivial module tensor its own group algebra

Let `K` be a field, `G` a group and `M` a left `K[G]`-module which is also a `K`-vector space, the
two structures being compatible (`IsScalarTower K K[G] M`).  Then the natural map

`(K[G] ⧸ I_{K[G]}) ⊗[K] M → M,  (x + I) ⊗ m ↦ ε(x) • m`

is an isomorphism of `K[G]`-modules, where `K[G] ⧸ I_{K[G]}` carries the diagonal `K[G]`-action
`g • (n ⊗ m) = (g • n) ⊗ (g • m)` (see `Submission/Work/ORLyndon/DiagTensor.lean`).

The two maps are inverse to each other; this is the statement of `Work.ORLyndon.trivialTensorEquiv`,
which is used to show that `HasProjDimLE (K[G]) M` follows from `HasProjDimLE (K[G]) K` (the trivial
module).

## Main results

* `Work.ORLyndon.trivialTensorEquiv`:
  `(K[G] ⧸ I_{K[G]}) ⊗[K] M ≃ₗ[K[G]] M`.

## Implementation notes

Mathlib's "left" action on a tensor product `n ⊗ₜ m ↦ (a • n) ⊗ₜ m` is *not* the diagonal action
needed here; as in `Submission/Work/ORLyndon/DiagTensor.lean` we remove the corresponding instances
so that the module structure is the diagonal one (the instance `Work.ORLyndon.diagModule`).
-/

set_option autoImplicit false

attribute [-instance] TensorProduct.leftModule TensorProduct.leftDistribMulAction
  TensorProduct.leftHasSMul

open TensorProduct MonoidAlgebra

namespace Work.ORLyndon

universe u v

variable {K : Type v} [Field K] {G : Type u} [Group G]

/-- A group element acts trivially on the class of `1` in `K[G] ⧸ I_{K[G]}`. -/
theorem trivialTensorEquiv_smul_one_eq_one (g : G) :
    MonoidAlgebra.single g (1 : K)
      • (1 : MonoidAlgebra K G ⧸ augIdeal K G) = 1 := by
  have h1 : (1 : MonoidAlgebra K G ⧸ augIdeal K G)
      = Ideal.Quotient.mk (augIdeal K G) (1 : MonoidAlgebra K G) :=
    (map_one (Ideal.Quotient.mk (augIdeal K G))).symm
  rw [h1, smul_mk_augIdeal, mul_one]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (by
    rw [mem_augIdeal, map_sub, augmentation_single, augmentation_one, sub_self])

section Main

variable {M : Type (max u v)} [AddCommGroup M] [Module K M]
  [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M]

/-- The `K`-linear map `(x + I) ⊗ m ↦ ε x • m`. -/
noncomputable def trivialTensorEquiv_phiLin (K : Type v) [Field K] (G : Type u) [Group G]
    (M : Type (max u v)) [AddCommGroup M] [Module K M] :
    (MonoidAlgebra K G ⧸ augIdeal K G) ⊗[K] M →ₗ[K] M :=
  (TensorProduct.lid K M).toLinearMap.comp
    (TensorProduct.map (augQuot K G) (LinearMap.id : M →ₗ[K] M))

theorem trivialTensorEquiv_phiLin_tmul (K : Type v) [Field K] (G : Type u) [Group G]
    (M : Type (max u v)) [AddCommGroup M] [Module K M]
    (q : MonoidAlgebra K G ⧸ augIdeal K G) (m : M) :
    trivialTensorEquiv_phiLin K G M (q ⊗ₜ[K] m) = augQuot K G q • m := by
  simp [trivialTensorEquiv_phiLin]

/-- The `K[G]`-linear map `(x + I) ⊗ m ↦ ε x • m`, for the diagonal action on the tensor product. -/
noncomputable def trivialTensorEquiv_phi (K : Type v) [Field K] (G : Type u) [Group G]
    (M : Type (max u v)) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M] :
    (MonoidAlgebra K G ⧸ augIdeal K G) ⊗[K] M →ₗ[MonoidAlgebra K G] M :=
  MonoidAlgebra.equivariantOfLinearOfComm (R := K) (M := G) (trivialTensorEquiv_phiLin K G M) (by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, smul_add, ha, hb]
    | tmul q m =>
      rw [diagModule_single_tmul, trivialTensorEquiv_phiLin_tmul, trivialTensorEquiv_phiLin_tmul,
        augQuot_smul, augmentation_single, one_mul, smul_algebra_smul_comm])

/-- The `K`-linear map `m ↦ (1 + I) ⊗ m`. -/
noncomputable def trivialTensorEquiv_psiLin (K : Type v) [Field K] (G : Type u) [Group G]
    (M : Type (max u v)) [AddCommGroup M] [Module K M] :
    M →ₗ[K] (MonoidAlgebra K G ⧸ augIdeal K G) ⊗[K] M :=
  TensorProduct.mk K (MonoidAlgebra K G ⧸ augIdeal K G) M
    (1 : MonoidAlgebra K G ⧸ augIdeal K G)

theorem trivialTensorEquiv_psiLin_apply (K : Type v) [Field K] (G : Type u) [Group G]
    (M : Type (max u v)) [AddCommGroup M] [Module K M] (m : M) :
    trivialTensorEquiv_psiLin K G M m
      = (1 : MonoidAlgebra K G ⧸ augIdeal K G) ⊗ₜ[K] m := rfl

/-- The `K[G]`-linear map `m ↦ (1 + I) ⊗ m`, for the diagonal action on the tensor product. -/
noncomputable def trivialTensorEquiv_psi (K : Type v) [Field K] (G : Type u) [Group G]
    (M : Type (max u v)) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M] :
    M →ₗ[MonoidAlgebra K G] (MonoidAlgebra K G ⧸ augIdeal K G) ⊗[K] M :=
  MonoidAlgebra.equivariantOfLinearOfComm (R := K) (M := G) (trivialTensorEquiv_psiLin K G M) (by
    intro g m
    rw [trivialTensorEquiv_psiLin_apply, trivialTensorEquiv_psiLin_apply,
      diagModule_single_tmul, trivialTensorEquiv_smul_one_eq_one])

theorem trivialTensorEquiv_phi_psi (K : Type v) [Field K] (G : Type u) [Group G]
    (M : Type (max u v)) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M] :
    (trivialTensorEquiv_phi K G M).comp (trivialTensorEquiv_psi K G M) = LinearMap.id := by
  ext m
  simp only [LinearMap.comp_apply, LinearMap.id_apply, trivialTensorEquiv_phi,
    trivialTensorEquiv_psi, MonoidAlgebra.equivariantOfLinearOfComm_apply,
    trivialTensorEquiv_psiLin_apply, trivialTensorEquiv_phiLin_tmul, augQuot_one, one_smul]

theorem trivialTensorEquiv_psi_phi (K : Type v) [Field K] (G : Type u) [Group G]
    (M : Type (max u v)) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M] :
    (trivialTensorEquiv_psi K G M).comp (trivialTensorEquiv_phi K G M) = LinearMap.id := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul q m =>
    simp only [LinearMap.comp_apply, LinearMap.id_apply, trivialTensorEquiv_phi,
      trivialTensorEquiv_psi, MonoidAlgebra.equivariantOfLinearOfComm_apply,
      trivialTensorEquiv_phiLin_tmul, trivialTensorEquiv_psiLin_apply]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', augQuot_smul_one]

/-- The isomorphism `(K[G] ⧸ I_{K[G]}) ⊗[K] M ≃ₗ[K[G]] M`. -/
noncomputable def trivialTensorEquivAux (K : Type v) [Field K] (G : Type u) [Group G]
    (M : Type (max u v)) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M] :
    (MonoidAlgebra K G ⧸ augIdeal K G) ⊗[K] M ≃ₗ[MonoidAlgebra K G] M :=
  LinearEquiv.ofLinearMap (trivialTensorEquiv_phi K G M) (trivialTensorEquiv_psi K G M)
    (trivialTensorEquiv_phi_psi K G M) (trivialTensorEquiv_psi_phi K G M)

end Main

theorem trivialTensorEquiv {K : Type v} [Field K] {G : Type u} [Group G] {M : Type (max u v)} [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M] : Nonempty ((TensorProduct K (MonoidAlgebra K G ⧸ Work.ORLyndon.augIdeal K G) M) ≃ₗ[MonoidAlgebra K G] M) := ⟨trivialTensorEquivAux K G M⟩

end Work.ORLyndon
