import Mathlib
import Submission.Work.ORLyndon.DiagTensor

set_option autoImplicit false
set_option linter.unusedVariables false
open TensorProduct

attribute [-instance] TensorProduct.leftModule TensorProduct.leftDistribMulAction
  TensorProduct.leftHasSMul

namespace Work.ORLyndon
universe u v

variable {K : Type v} [Field K] {G : Type u} [Group G] {M : Type (max u v)}
  [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
  [IsScalarTower K (MonoidAlgebra K G) M]

noncomputable def dsB : Module.Basis (Module.Free.ChooseBasisIndex K M) K M :=
  Module.Free.chooseBasis K M

noncomputable def dsVtens (g : G) :
    M →ₗ[K] (Module.Free.ChooseBasisIndex K M →₀ MonoidAlgebra K G) :=
  (Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle (M := G) g)).comp
    (dsB.repr.toLinearMap.comp (MonoidAlgebra.GroupSMul.linearMap K M g⁻¹))

noncomputable def dsFerm :
    MonoidAlgebra K G →ₗ[K]
      (M →ₗ[K] (Module.Free.ChooseBasisIndex K M →₀ MonoidAlgebra K G)) :=
  (Module.Basis.constr (MonoidAlgebra.basis G K) K) dsVtens

noncomputable def dsE : MonoidAlgebra K G ⊗[K] M →ₗ[K]
    (Module.Free.ChooseBasisIndex K M →₀ MonoidAlgebra K G) :=
  TensorProduct.lift dsFerm

noncomputable def dsEinv :
    (Module.Free.ChooseBasisIndex K M →₀ MonoidAlgebra K G) →ₗ[K]
      (MonoidAlgebra K G ⊗[K] M) :=
  Finsupp.lsum K (fun i =>
    { toFun := fun a => a • (1 ⊗ₜ[K] dsB i)
      map_add' := fun a b => add_smul a b (1 ⊗ₜ[K] dsB i)
      map_smul' := fun c a => IsScalarTower.smul_assoc c a (1 ⊗ₜ[K] dsB i) })

noncomputable def dsE0 :
    Module.Basis (G × Module.Free.ChooseBasisIndex K M) K (MonoidAlgebra K G ⊗[K] M) :=
  Module.Basis.tensorProduct (MonoidAlgebra.basis G K) dsB

theorem dsE_single_tmul (h : G) (m : M) :
    dsE (MonoidAlgebra.single h (1:K) ⊗ₜ[K] m) = dsVtens (K := K) (G := G) (M := M) h m := by
  rw [dsE, TensorProduct.lift.tmul]
  exact congrArg (fun f => f m)
    (Module.Basis.constr_basis (MonoidAlgebra.basis G K) K
      (dsVtens (K := K) (G := G) (M := M)) h)

theorem dsEinv_apply (y : Module.Free.ChooseBasisIndex K M →₀ MonoidAlgebra K G) :
    dsEinv y = y.sum (fun i a => a • (1 ⊗ₜ[K] dsB i)) := by
  rw [dsEinv, Finsupp.lsum_apply]
  exact Finsupp.sum_congr (fun i a => rfl)

theorem dsE_one_tmul (i : Module.Free.ChooseBasisIndex K M) :
    dsE ((1 : MonoidAlgebra K G) ⊗ₜ[K] dsB i) = Finsupp.single i (1 : MonoidAlgebra K G) := by
  have hone : (1 : MonoidAlgebra K G) = MonoidAlgebra.single (1 : G) (1 : K) :=
    MonoidAlgebra.one_def
  rw [hone, dsE_single_tmul (K := K) (G := G) (M := M) 1 (dsB i)]
  rw [dsVtens, LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply,
    MonoidAlgebra.GroupSMul.linearMap_apply, inv_one]
  rw [← hone, one_smul]
  change Finsupp.mapRange (MonoidAlgebra.lsingle (1 : G)) _ (dsB.repr (dsB i)) =
    Finsupp.single i (1 : MonoidAlgebra K G)
  rw [Module.Basis.repr_self, Finsupp.mapRange_single, MonoidAlgebra.lsingle_apply, hone]

theorem dsVtens_smul (g h : G) (m : M) :
    MonoidAlgebra.single g (1:K) • dsVtens (K := K) (G := G) (M := M) h m
      = dsVtens (K := K) (G := G) (M := M) (g * h) (MonoidAlgebra.single g (1:K) • m) := by
  have harg : MonoidAlgebra.GroupSMul.linearMap K M ((g * h)⁻¹)
      (MonoidAlgebra.single g (1:K) • m)
      = MonoidAlgebra.GroupSMul.linearMap K M (h⁻¹) m := by
    rw [← MonoidAlgebra.GroupSMul.linearMap_apply K M g m]
    rw [MonoidAlgebra.GroupSMul.linearMap_apply, MonoidAlgebra.GroupSMul.linearMap_apply,
      MonoidAlgebra.GroupSMul.linearMap_apply, ← mul_smul]
    congr 1
    rw [MonoidAlgebra.single_mul_single, mul_one, mul_inv_rev, mul_assoc, inv_mul_cancel,
      mul_one]
  simp only [dsVtens, LinearMap.comp_apply]
  rw [harg]
  ext j
  simp only [Finsupp.smul_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    MonoidAlgebra.lsingle_apply, smul_eq_mul, MonoidAlgebra.single_mul_single, one_mul]

theorem diag_smul_map (g : G) (x : MonoidAlgebra K G ⊗[K] M) :
    MonoidAlgebra.single g (1:K) • x
      = TensorProduct.map (MonoidAlgebra.GroupSMul.linearMap K (MonoidAlgebra K G) g)
          (MonoidAlgebra.GroupSMul.linearMap K M g) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul a m =>
      rw [diagModule_single_tmul, TensorProduct.map_tmul]
      rfl

theorem dsE_equivariant (g : G) (x : MonoidAlgebra K G ⊗[K] M) :
    dsE (MonoidAlgebra.single g (1:K) • x) = MonoidAlgebra.single g (1:K) • dsE x := by
  let smulLin : (Module.Free.ChooseBasisIndex K M →₀ MonoidAlgebra K G) →ₗ[K]
      (Module.Free.ChooseBasisIndex K M →₀ MonoidAlgebra K G) :=
    { toFun := fun y => MonoidAlgebra.single g (1:K) • y
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun c a => (smul_comm c (MonoidAlgebra.single g (1:K)) a).symm }
  have hsmulLin : ∀ y, smulLin y = MonoidAlgebra.single g (1:K) • y := fun y => rfl
  have key : ∀ (p : G × Module.Free.ChooseBasisIndex K M),
      (dsE.comp (TensorProduct.map (MonoidAlgebra.GroupSMul.linearMap K (MonoidAlgebra K G) g)
        (MonoidAlgebra.GroupSMul.linearMap K M g))) (dsE0 (K := K) (G := G) (M := M) p)
      = (smulLin.comp dsE) (dsE0 (K := K) (G := G) (M := M) p) := by
    rintro ⟨h, i⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, dsE0, Module.Basis.tensorProduct_apply,
      show (MonoidAlgebra.basis G K) h = MonoidAlgebra.single h (1:K) from rfl,
      TensorProduct.map_tmul, MonoidAlgebra.GroupSMul.linearMap_apply,
      MonoidAlgebra.GroupSMul.linearMap_apply, smul_eq_mul, MonoidAlgebra.single_mul_single,
      mul_one, hsmulLin]
    rw [dsE_single_tmul (K := K) (G := G) (M := M) (g * h)
        (MonoidAlgebra.single g (1:K) • dsB i),
      dsE_single_tmul (K := K) (G := G) (M := M) h (dsB i),
      dsVtens_smul (K := K) (G := G) (M := M) g h (dsB i)]
  have hmain := Module.Basis.ext (dsE0 (K := K) (G := G) (M := M)) key
  rw [diag_smul_map (K := K) (G := G) (M := M) g x]
  have h2 := congrFun (congrArg DFunLike.coe hmain) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hsmulLin] at h2
  exact h2

end Work.ORLyndon

namespace Work.ORLyndon

universe u v

variable {K : Type v} [Field K] {G : Type u} [Group G] {M : Type (max u v)}
  [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
  [IsScalarTower K (MonoidAlgebra K G) M]

noncomputable def dsElin : MonoidAlgebra K G ⊗[K] M →ₗ[MonoidAlgebra K G]
    (Module.Free.ChooseBasisIndex K M →₀ MonoidAlgebra K G) :=
  MonoidAlgebra.equivariantOfLinearOfComm dsE dsE_equivariant

theorem dsElin_apply (x : MonoidAlgebra K G ⊗[K] M) : dsElin x = dsE x := rfl

theorem tmul_finsupp_sum {ι : Type*} (x : MonoidAlgebra K G) (v : ι → M) (c : ι →₀ K) :
    x ⊗ₜ[K] (c.sum fun j b => b • v j) = c.sum fun j b => b • (x ⊗ₜ[K] v j) := by
  rw [← TensorProduct.mk_apply (R := K) (M := MonoidAlgebra K G) (N := M) x]
  rw [map_finsuppSum]
  exact Finsupp.sum_congr (fun j b => by rw [map_smul, TensorProduct.mk_apply])

theorem gsm_finsupp_sum {ι : Type*} (g : G) (v : ι → M) (c : ι →₀ K) :
    MonoidAlgebra.single g (1:K) • (c.sum fun j b => b • v j)
      = c.sum fun j b => b • (MonoidAlgebra.single g (1:K) • v j) := by
  rw [← MonoidAlgebra.GroupSMul.linearMap_apply K M g, map_finsuppSum]
  exact Finsupp.sum_congr (fun j b => by
    rw [map_smul, MonoidAlgebra.GroupSMul.linearMap_apply K M g])

theorem dsE_einv (y : Module.Free.ChooseBasisIndex K M →₀ MonoidAlgebra K G) :
    dsE (dsEinv y) = y := by
  rw [dsEinv_apply]
  have h1 : dsE (y.sum (fun i a => a • ((1 : MonoidAlgebra K G) ⊗ₜ[K] dsB i)))
      = y.sum (fun i a => a • dsE ((1 : MonoidAlgebra K G) ⊗ₜ[K] dsB i)) := by
    rw [← dsElin_apply]
    rw [map_finsuppSum]
    exact Finsupp.sum_congr (fun i a => by rw [map_smul, dsElin_apply])
  rw [h1]
  rw [Finsupp.sum_congr (fun i a => by
    rw [dsE_one_tmul (K := K) (G := G) (M := M) i, Finsupp.smul_single', mul_one])]
  exact Finsupp.sum_single y

