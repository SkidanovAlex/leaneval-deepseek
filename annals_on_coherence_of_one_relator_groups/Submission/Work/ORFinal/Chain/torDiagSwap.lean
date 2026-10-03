import Mathlib
import Submission.Work.ORFlatness.DiagonalRight
import Submission.Work.ORBridgeTor.DiagRightCompat
import Submission.Work.ORHomAlg.JL52.jl_5_2_2
import Submission.Work.ORHomAlg.leftDerived_comp_of_preservesProjectiveObjects
import Submission.Work.ORFinal.Chain.diagTensorObjIso

/-- v4.35 port: `TensorProduct.induction_on` lost `@[elab_as_elim]` when deprecated. -/
@[elab_as_elim] private theorem tpInductionOn' {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] {motive : TensorProduct R M N → Prop}
    (z : TensorProduct R M N) (zero : motive 0) (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z zero tmul add


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open TensorProduct MulOpposite Work.ORHomAlg
open scoped TensorProduct
open CategoryTheory

namespace Work.ORFinal.Chain

universe u

section Setup

variable (K : Type u) [Field K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
variable [Module (MonoidAlgebra K G)ᵐᵒᵖ S]
variable (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
variable [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M]

/-- The `K`-action on `S` and the right `K[G]`-action are a scalar tower. -/
theorem SRsmul (hSright : ∀ (x : MonoidAlgebra K G) (s : S), (MulOpposite.op x) • s = s * φ x)
    (c : K) (a : (MonoidAlgebra K G)ᵐᵒᵖ) (s : S) :
    (c • a) • s = c • (a • s) := by
  refine MulOpposite.rec' (fun r => ?_) a
  rw [← MulOpposite.op_smul, hSright (c • r) s, hSright r s, map_smul]
  simp only [Algebra.smul_def]
  rw [← mul_assoc, ← Algebra.commutes c s, mul_assoc]

/-- The diagonal `K[G]`-action on `M ⊗[K] X` is a scalar tower over `K`. -/
theorem diagTower (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] : IsScalarTower K (MonoidAlgebra K G) (M ⊗[K] X) where
  smul_assoc c r z := by
    rw [Work.ORHomAlg.JL52.diag_smul_def, Work.ORHomAlg.JL52.diag_smul_def,
      Work.ORHomAlg.JL52.diagRingHom_smul, LinearMap.smul_apply]

/-- K-compatibility of `BalancedTensor.tmul` on `BalancedTensor R (S ⊗[K] M) X`. -/
theorem tmul_k_smul (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [IsScalarTower K (MonoidAlgebra K G) X]
    (z : S ⊗[K] M) (x : X) (c : K) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    (BalancedTensor.tmul (MonoidAlgebra K G) (c • z) x :
        BalancedTensor (MonoidAlgebra K G) (S ⊗[K] M) X)
      = BalancedTensor.tmul (MonoidAlgebra K G) z (c • x) := by
  letI := Work.ORFlatness.diagRightModule K G S φ M
  have hz : (algebraMap K ((MonoidAlgebra K G)ᵐᵒᵖ)) c • z = c • z :=
    Work.ORBridgeTor.diagRightModule_algebraMap_smul K G S φ M c z
  have hx : (algebraMap K (MonoidAlgebra K G)) c • x = c • x :=
    IsScalarTower.algebraMap_smul (MonoidAlgebra K G) c x
  rw [← hz, ← hx]
  exact BalancedTensor.tmul_smul z (algebraMap K (MonoidAlgebra K G) c) x

/-- The `K`-action on `S` commutes with the right `K[G]`-action. -/
theorem SKsmul (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x) :
    SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ S where
  smul_comm c a s := by
    refine MulOpposite.rec' (fun r => ?_) a
    rw [hSright r s, hSright r (c • s), Algebra.smul_def, Algebra.smul_def, mul_assoc]

/-- `BalancedTensor.tmul` on `BalancedTensor R S (M ⊗[K] X)` is `K`-balanced. -/
theorem tmul_ksmul' (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    (c : K) (s : S) (y : TensorProduct K M X) :
    BalancedTensor.tmul (MonoidAlgebra K G) (c • s) y =
      BalancedTensor.tmul (MonoidAlgebra K G) s (c • y) := by
  have hcy : (algebraMap K (MonoidAlgebra K G) c) • y = c • y := by
    change (Work.ORHomAlg.JL52.diagRingHom M X) (algebraMap K (MonoidAlgebra K G) c) y = c • y
    rw [show algebraMap K (MonoidAlgebra K G) c = c • (1 : MonoidAlgebra K G) from
      Algebra.algebraMap_eq_smul_one c, Work.ORHomAlg.JL52.diagRingHom_smul]
    simp
  have hs : c • s = MulOpposite.op (algebraMap K (MonoidAlgebra K G) c) • s := by
    rw [hSright (algebraMap K (MonoidAlgebra K G) c) s, φ.commutes c, Algebra.smul_def,
      Algebra.commutes c s]
  rw [hs, BalancedTensor.tmul_smul]
  show BalancedTensor.tmul (MonoidAlgebra K G) s
    ((algebraMap K (MonoidAlgebra K G) c) • y) =
    BalancedTensor.tmul (MonoidAlgebra K G) s (c • y)
  rw [hcy]

noncomputable def fwdBfun (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
      Work.ORFlatness.diagRightModule K G S φ M
    letI : SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
      Work.ORBridgeTor.smulCommClass_diagRightModule K G S φ M
    S → (M →ₗ[K] X →ₗ[K] BalancedTensor (MonoidAlgebra K G) (TensorProduct K S M) X) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  haveI hsc : SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORBridgeTor.smulCommClass_diagRightModule K G S φ M
  exact fun s =>
    { toFun := fun m =>
      { toFun := fun x => BalancedTensor.tmul (MonoidAlgebra K G) (s ⊗ₜ[K] m) x
        map_add' := by intro x y; rw [BalancedTensor.tmul_add']
        map_smul' := by
          intro c x
          rw [← tmul_k_smul (K := K) (G := G) (S := S) (φ := φ) (M := M) X
            (s ⊗ₜ[K] m) x c, ← BalancedTensor.smul_tmul]
          rfl }
      map_add' := by
        intro m1 m2
        ext x
        change BalancedTensor.tmul (MonoidAlgebra K G) (s ⊗ₜ[K] (m1 + m2)) x =
          BalancedTensor.tmul (MonoidAlgebra K G) (s ⊗ₜ[K] m1) x +
            BalancedTensor.tmul (MonoidAlgebra K G) (s ⊗ₜ[K] m2) x
        rw [TensorProduct.tmul_add, BalancedTensor.tmul_add]
      map_smul' := by
        intro c m
        ext x
        change BalancedTensor.tmul (MonoidAlgebra K G) (s ⊗ₜ[K] (c • m)) x =
          (c • BalancedTensor.tmul (MonoidAlgebra K G) (s ⊗ₜ[K] m) x :
            BalancedTensor (MonoidAlgebra K G) (TensorProduct K S M) X)
        rw [TensorProduct.tmul_smul, ← BalancedTensor.smul_tmul] }

noncomputable def fwdAux (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    S →+ (TensorProduct K M X) →+
      BalancedTensor (MonoidAlgebra K G) (TensorProduct K S M) X := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  haveI hsc : SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORBridgeTor.smulCommClass_diagRightModule K G S φ M
  exact
  { toFun := fun s => (TensorProduct.lift (fwdBfun (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X) s)).toAddMonoidHom
    map_zero' := by
      apply AddMonoidHom.ext
      intro y
      rw [AddMonoidHom.zero_apply]
      change (TensorProduct.lift (fwdBfun (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X) 0)) y = 0
      refine tpInductionOn' y ?_ ?_ ?_
      · rw [map_zero]
      · intro m x
        change (TensorProduct.lift (fwdBfun (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X) 0)) (m ⊗ₜ[K] x) = 0
        rw [TensorProduct.lift.tmul]
        show BalancedTensor.tmul (MonoidAlgebra K G) ((0 : S) ⊗ₜ[K] m) x = 0
        rw [TensorProduct.zero_tmul, BalancedTensor.tmul_zero]
      · intro y1 y2 h1 h2; rw [map_add, h1, h2, add_zero]
    map_add' := by
      intro s1 s2
      apply AddMonoidHom.ext
      intro y
      rw [AddMonoidHom.add_apply]
      change (TensorProduct.lift (fwdBfun (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X) (s1 + s2))) y =
        (TensorProduct.lift (fwdBfun (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X) s1)) y +
        (TensorProduct.lift (fwdBfun (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X) s2)) y
      refine tpInductionOn' y ?_ ?_ ?_
      · rw [map_zero, map_zero, map_zero, add_zero]
      · intro m x
        rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        show BalancedTensor.tmul (MonoidAlgebra K G) ((s1 + s2) ⊗ₜ[K] m) x =
          BalancedTensor.tmul (MonoidAlgebra K G) (s1 ⊗ₜ[K] m) x +
            BalancedTensor.tmul (MonoidAlgebra K G) (s2 ⊗ₜ[K] m) x
        rw [TensorProduct.add_tmul, BalancedTensor.tmul_add]
      · intro y1 y2 h1 h2; rw [map_add, map_add, map_add, h1, h2]; abel }

theorem fwdAux_tmul (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    (s : S) (m : M) (x : X) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    fwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X) s (m ⊗ₜ[K] x) =
      BalancedTensor.tmul (MonoidAlgebra K G) (s ⊗ₜ[K] m) x := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  haveI hsc : SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORBridgeTor.smulCommClass_diagRightModule K G S φ M
  change (TensorProduct.lift (fwdBfun (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X) s)) (m ⊗ₜ[K] x) = _
  rw [TensorProduct.lift.tmul]
  rfl

theorem fwdAux_hf (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    ∀ (s : S) (r : MonoidAlgebra K G) (y : TensorProduct K M X),
      fwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
          (MulOpposite.op r • s) y =
        fwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X) s (r • y) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  haveI htw : IsScalarTower K (MonoidAlgebra K G) (M ⊗[K] X) :=
    diagTower (K := K) (G := G) (M := M) X
  have hsmul_add : ∀ (a : MonoidAlgebra K G) (u v : M ⊗[K] X),
      a • (u + v) = a • u + a • v := by
    intro a u v
    rw [Work.ORHomAlg.JL52.diag_smul_def, Work.ORHomAlg.JL52.diag_smul_def,
      Work.ORHomAlg.JL52.diag_smul_def, map_add]
  have hsmul_zero : ∀ (a : MonoidAlgebra K G), a • (0 : M ⊗[K] X) = 0 := by
    intro a
    rw [Work.ORHomAlg.JL52.diag_smul_def, map_zero]
  intro s r
  refine MonoidAlgebra.induction_on (motive := fun r =>
    ∀ y : TensorProduct K M X,
      fwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
          (MulOpposite.op r • s) y =
        fwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X) s (r • y)) r ?_ ?_ ?_
  · intro g y
    rw [MonoidAlgebra.of_apply, hSright (MonoidAlgebra.single g (1 : K)) s]
    refine tpInductionOn' y ?_ ?_ ?_
    · rw [map_zero, hsmul_zero, map_zero]
    · intro m x
      rw [Work.ORHomAlg.JL52.diag_smul_single_tmul, fwdAux_tmul, fwdAux_tmul]
      rw [← BalancedTensor.tmul_smul (s ⊗ₜ[K] (MonoidAlgebra.single g (1 : K) • m))
        (MonoidAlgebra.single g (1 : K)) x]
      congr 1
      rw [Work.ORFlatness.diagRightModule_op_single_tmul]
      rw [← mul_smul, MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul,
        ← MonoidAlgebra.one_def, one_smul]
      congr 1
    · intro y1 y2 h1 h2
      rw [map_add, hsmul_add, map_add, h1, h2]
  · intro r1 r2 h1 h2 y
    have e1 : (MulOpposite.op (r1 + r2)) • s =
        MulOpposite.op r1 • s + MulOpposite.op r2 • s := by
      rw [MulOpposite.op_add, add_smul]
    rw [e1, map_add, AddMonoidHom.add_apply, h1 y, h2 y, add_smul, map_add]
  · intro c r h y
    rw [MulOpposite.op_smul, SRsmul (K := K) (G := G) (S := S) (φ := φ) hSright c
      (MulOpposite.op r) s]
    have hc : fwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
          (c • (MulOpposite.op r • s)) y =
        fwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
          (MulOpposite.op r • s) (c • y) := by
      refine tpInductionOn' y ?_ ?_ ?_
      · rw [map_zero, smul_zero, map_zero]
      · intro m x
        rw [TensorProduct.smul_tmul', fwdAux_tmul, fwdAux_tmul, TensorProduct.smul_tmul]
      · intro y1 y2 h1 h2; rw [map_add, smul_add, map_add, h1, h2]
    rw [hc, h (c • y), IsScalarTower.smul_assoc c r y, ← smul_comm c r y]

noncomputable def fwdMap (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    BalancedTensor (MonoidAlgebra K G) S (TensorProduct K M X) →ₗ[ℤ]
      BalancedTensor (MonoidAlgebra K G) (TensorProduct K S M) X :=
  BalancedTensor.lift (fwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X))
    (fwdAux_hf (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X))

theorem fwdMap_tmul (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    (s : S) (m : M) (x : X) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    fwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
        (BalancedTensor.tmul (MonoidAlgebra K G) s (m ⊗ₜ[K] x)) =
      BalancedTensor.tmul (MonoidAlgebra K G) (s ⊗ₜ[K] m) x := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  rw [fwdMap, BalancedTensor.lift_tmul, fwdAux_tmul]

noncomputable def bwdG (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    S →+ M →+ (X →+ BalancedTensor (MonoidAlgebra K G) S (TensorProduct K M X)) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  refine
  { toFun := fun s =>
    { toFun := fun m =>
      { toFun := fun x => BalancedTensor.tmul (MonoidAlgebra K G) s (m ⊗ₜ[K] x)
        map_zero' := by rw [TensorProduct.tmul_zero, BalancedTensor.zero_tmul]
        map_add' := by intro x1 x2; rw [TensorProduct.tmul_add, BalancedTensor.tmul_add'] }
      map_zero' := by
        refine AddMonoidHom.ext fun x => ?_
        show BalancedTensor.tmul (MonoidAlgebra K G) s ((0 : M) ⊗ₜ[K] x) = 0
        rw [TensorProduct.zero_tmul, BalancedTensor.zero_tmul]
      map_add' := by
        intro m1 m2
        refine AddMonoidHom.ext fun x => ?_
        show BalancedTensor.tmul (MonoidAlgebra K G) s ((m1 + m2) ⊗ₜ[K] x) =
          BalancedTensor.tmul (MonoidAlgebra K G) s (m1 ⊗ₜ[K] x) +
            BalancedTensor.tmul (MonoidAlgebra K G) s (m2 ⊗ₜ[K] x)
        rw [TensorProduct.add_tmul, BalancedTensor.tmul_add'] }
    map_zero' := by
      refine AddMonoidHom.ext fun m => ?_
      refine AddMonoidHom.ext fun x => ?_
      show BalancedTensor.tmul (MonoidAlgebra K G) (0 : S) (m ⊗ₜ[K] x) = 0
      rw [BalancedTensor.tmul_zero]
    map_add' := by
      intro s1 s2
      refine AddMonoidHom.ext fun m => ?_
      refine AddMonoidHom.ext fun x => ?_
      show BalancedTensor.tmul (MonoidAlgebra K G) (s1 + s2) (m ⊗ₜ[K] x) =
        BalancedTensor.tmul (MonoidAlgebra K G) s1 (m ⊗ₜ[K] x) +
          BalancedTensor.tmul (MonoidAlgebra K G) s2 (m ⊗ₜ[K] x)
      rw [BalancedTensor.tmul_add] }

theorem bwdG_hf (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    (c : K) (s : S) (m : M) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    bwdG (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
        (c • s) m =
      bwdG (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
        s (c • m) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  refine AddMonoidHom.ext fun x => ?_
  show BalancedTensor.tmul (MonoidAlgebra K G) (c • s) (m ⊗ₜ[K] x) =
    BalancedTensor.tmul (MonoidAlgebra K G) s ((c • m) ⊗ₜ[K] x)
  rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  exact tmul_ksmul' (K := K) (G := G) (S := S) (φ := φ) (M := M) hSright X c s
    (m ⊗ₜ[K] x)

theorem bwdG_tmul (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    (s : S) (m : M) (x : X) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    bwdG (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X) s m x =
      BalancedTensor.tmul (MonoidAlgebra K G) s (m ⊗ₜ[K] x) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  rfl

noncomputable def bwdAux (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    (TensorProduct K S M) →+ (X →+
      BalancedTensor (MonoidAlgebra K G) S (TensorProduct K M X)) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  exact TensorProduct.liftAddHom (bwdG (K := K) (G := G) (S := S) (φ := φ) (M := M)
    (hSright := hSright) (X := X))
    (bwdG_hf (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X))

theorem bwdAux_tmul (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    (s : S) (m : M) (x : X) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    bwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
        (s ⊗ₜ[K] m) x =
      BalancedTensor.tmul (MonoidAlgebra K G) s (m ⊗ₜ[K] x) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  rw [bwdAux, TensorProduct.liftAddHom_tmul, bwdG_tmul]

theorem bwdAux_kbal (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    (c : K) (z : TensorProduct K S M) (x : X) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    bwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
        (c • z) x =
      bwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
        z (c • x) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    rw [TensorProduct.smul_tmul', bwdAux_tmul, bwdAux_tmul, ← TensorProduct.smul_tmul,
      ← TensorProduct.smul_tmul',
      tmul_ksmul' (K := K) (G := G) (S := S) (φ := φ) (M := M) hSright X c s (m ⊗ₜ[K] x)]
  | add z1 z2 h1 h2 =>
    rw [smul_add, map_add, AddMonoidHom.add_apply, h1, h2, map_add, AddMonoidHom.add_apply]

theorem bwdAux_hf (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    ∀ (z : TensorProduct K S M) (r : MonoidAlgebra K G) (x : X),
      bwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
          (MulOpposite.op r • z) x =
        bwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
          z (r • x) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  haveI htw : IsScalarTower K (MonoidAlgebra K G) (M ⊗[K] X) :=
    diagTower (K := K) (G := G) (M := M) X
  intro z r
  refine MonoidAlgebra.induction_on (motive := fun r =>
    ∀ (x : X),
      bwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
          (MulOpposite.op r • z) x =
        bwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
          z (r • x)) r ?_ ?_ ?_
  · intro g x
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      rw [MonoidAlgebra.of_apply, Work.ORFlatness.diagRightModule_op_single_tmul]
      simp only [Work.ORFlatness.gElemR]
      rw [← hSright (MonoidAlgebra.single g (1 : K)) s]
      rw [bwdAux_tmul, bwdAux_tmul, BalancedTensor.tmul_smul,
        Work.ORHomAlg.JL52.diag_smul_single_tmul]
      congr 1
      rw [← mul_smul, MonoidAlgebra.single_mul_single, mul_inv_cancel, one_mul,
        ← MonoidAlgebra.one_def, one_smul]
    | add z1 z2 h1 h2 =>
      rw [smul_add, map_add, AddMonoidHom.add_apply, h1, h2, map_add, AddMonoidHom.add_apply]
  · intro r1 r2 h1 h2 x
    rw [MulOpposite.op_add, add_smul, map_add, AddMonoidHom.add_apply, h1 x, h2 x,
      add_smul, map_add]
  · intro c r h x
    haveI hstz : IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
      Work.ORBridgeTor.isScalarTower_diagRightModule K G S φ M
    rw [MulOpposite.op_smul, IsScalarTower.smul_assoc c (MulOpposite.op r) z,
      bwdAux_kbal, h (c • x), IsScalarTower.smul_assoc c r x, ← smul_comm c r x]

noncomputable def bwdMap (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    BalancedTensor (MonoidAlgebra K G) (TensorProduct K S M) X →ₗ[ℤ]
      BalancedTensor (MonoidAlgebra K G) S (TensorProduct K M X) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  exact BalancedTensor.lift (bwdAux (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X))
    (bwdAux_hf (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X))

theorem bwdMap_tmul (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    (s : S) (m : M) (x : X) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    bwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)
        (BalancedTensor.tmul (MonoidAlgebra K G) (s ⊗ₜ[K] m) x) =
      BalancedTensor.tmul (MonoidAlgebra K G) s (m ⊗ₜ[K] x) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  rw [bwdMap, BalancedTensor.lift_tmul, bwdAux_tmul]

theorem bwdMap_comp_fwdMap (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    (bwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)).comp
        (fwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X))
      = LinearMap.id := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  apply LinearMap.ext
  intro z
  refine BalancedTensor.induction_on z ?_ ?_ ?_
  · simp
  · intro a b ha hb
    rw [map_add, map_add, ha, hb]
  · intro s y
    refine tpInductionOn' y ?_ ?_ ?_
    · simp
    · intro m x
      rw [LinearMap.comp_apply, fwdMap_tmul, bwdMap_tmul]
      rfl
    · intro y1 y2 h1 h2
      rw [BalancedTensor.tmul_add', map_add, map_add, h1, h2]

theorem fwdMap_comp_bwdMap (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X : Type u) [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    (fwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X)).comp
        (bwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := X))
      = LinearMap.id := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  apply LinearMap.ext
  intro z
  refine BalancedTensor.induction_on z ?_ ?_ ?_
  · simp
  · intro a b ha hb
    rw [map_add, map_add, ha, hb]
  · intro z' x
    refine tpInductionOn' z' ?_ ?_ ?_
    · simp
    · intro s m
      rw [LinearMap.comp_apply, bwdMap_tmul, fwdMap_tmul]
      rfl
    · intro z1 z2 h1 h2
      rw [BalancedTensor.tmul_add, map_add, map_add, h1, h2]

theorem fwdMap_natural (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x)
    (X Y : ModuleCat (MonoidAlgebra K G)) (f : X ⟶ Y)
    (z : BalancedTensor (MonoidAlgebra K G) S ↥((Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) M).obj X)) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    fwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := ↥Y)
        (Work.ORHomAlg.BalancedTensor.lTensor (R := MonoidAlgebra K G) (M := S)
          ((Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) M).map f).hom z) =
      Work.ORHomAlg.BalancedTensor.lTensor (R := MonoidAlgebra K G)
          (M := TensorProduct K S M) f.hom
        (fwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := ↥X) z) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  revert z
  intro z
  refine BalancedTensor.induction_on z ?_ ?_ ?_
  · simp
  · intro a b ha hb
    rw [map_add, map_add, map_add, map_add, ha, hb]
  · intro s y
    refine tpInductionOn' y ?_ ?_ ?_
    · simp
    · intro m x
      rw [Work.ORHomAlg.BalancedTensor.lTensor_tmul]
      have hg : ((Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) M).map f).hom
          (m ⊗ₜ[K] x) = m ⊗ₜ[K] (f.hom x) :=
        LinearMap.lTensor_tmul M (Work.ORHomAlg.JL52.restrictK f.hom) m x
      rw [hg, fwdMap_tmul, fwdMap_tmul, Work.ORHomAlg.BalancedTensor.lTensor_tmul]
    · intro y1 y2 h1 h2
      rw [Work.ORHomAlg.BalancedTensor.tmul_add', map_add, map_add, map_add, map_add, h1, h2]

noncomputable def diagAssocIso (hSright : ∀ (x : MonoidAlgebra K G) (s : S),
      (MulOpposite.op x) • s = s * φ x) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    (Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) M) ⋙
        (Work.ORHomAlg.tensorLeftFunctor (R := MonoidAlgebra K G) S) ≅
      Work.ORHomAlg.tensorLeftFunctor (R := MonoidAlgebra K G) (TensorProduct K S M) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  refine NatIso.ofComponents (fun X => ?_) (fun {X Y} f => ?_)
  · exact LinearEquiv.toModuleIso
      { toFun := fwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := ↥X)
        invFun := bwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := ↥X)
        map_add' := (fwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := ↥X)).map_add
        map_smul' := (fwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := ↥X)).map_smul
        left_inv := fun z => congrArg (fun φ => φ z)
          (bwdMap_comp_fwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := ↥X))
        right_inv := fun z => congrArg (fun φ => φ z)
          (fwdMap_comp_bwdMap (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) (X := ↥X)) }
  · exact ModuleCat.hom_ext (LinearMap.ext
      (fun z => fwdMap_natural (K := K) (G := G) (S := S) (φ := φ) (M := M) (hSright := hSright) X Y f z))

theorem torDiagSwap_aux (K : Type u) [Field K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    [Module (MonoidAlgebra K G)ᵐᵒᵖ S]
    (hSright : ∀ (x : MonoidAlgebra K G) (s : S), (MulOpposite.op x) • s = s * φ x)
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M]
    (N : Type u) [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N]
    [IsScalarTower K (MonoidAlgebra K G) N] [SMulCommClass K (MonoidAlgebra K G) N]
    (hIso : Nonempty ((Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) M).obj
        (ModuleCat.of (MonoidAlgebra K G) N)
      ≅ ModuleCat.of (MonoidAlgebra K G) (TensorProduct K M N)))
    (k : ℕ) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    Nonempty (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) k S (TensorProduct K M N) ≃ₗ[ℤ]
      Work.ORHomAlg.Tor (R := MonoidAlgebra K G) k (TensorProduct K S M) N) := by
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S M) :=
    Work.ORFlatness.diagRightModule K G S φ M
  let α := diagAssocIso (K := K) (G := G) (S := S) (φ := φ) (M := M) hSright
  let β : (((Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) M) ⋙
      (Work.ORHomAlg.tensorLeftFunctor (R := MonoidAlgebra K G) S)).leftDerived k) ≅
      ((Work.ORHomAlg.tensorLeftFunctor (R := MonoidAlgebra K G)
        (TensorProduct K S M)).leftDerived k) :=
    { hom := NatTrans.leftDerived α.hom k
      inv := NatTrans.leftDerived α.inv k
      hom_inv_id := by
        rw [← NatTrans.leftDerived_comp, Iso.hom_inv_id α, NatTrans.leftDerived_id]
      inv_hom_id := by
        rw [← NatTrans.leftDerived_comp, Iso.inv_hom_id α, NatTrans.leftDerived_id] }
  haveI hproj : (Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) M).PreservesProjectiveObjects :=
    Work.ORHomAlg.JL52.diagTensor_preservesProjectiveObjects K G M
  haveI hhom : (Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) M).PreservesHomology :=
    Work.ORHomAlg.JL52.diagTensor_preservesHomology K G M
  obtain ⟨c⟩ := Work.ORHomAlg.leftDerived_comp_of_preservesProjectiveObjects
    (Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) M)
    (Work.ORHomAlg.tensorLeftFunctor (R := MonoidAlgebra K G) S)
    (ModuleCat.of (MonoidAlgebra K G) N) k
  obtain ⟨e⟩ := hIso
  exact ⟨((Functor.mapIso
      ((Work.ORHomAlg.tensorLeftFunctor (R := MonoidAlgebra K G) S).leftDerived k) e).symm
    ≪≫ c.symm ≪≫ β.app (ModuleCat.of (MonoidAlgebra K G) N)).toLinearEquiv⟩

/-- Swapping `S ⊗[K] M` past `M ⊗[K] -` is invisible to `Tor`: for a left `K[G]`-module `N`,
`Tor_k^{K[G]}(S, M ⊗_K N) ≃ Tor_k^{K[G]}(S ⊗_K M, N)`. -/
theorem torDiagSwap (K : Type u) [Field K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    [Module (MonoidAlgebra K G)ᵐᵒᵖ S]
    (hSright : ∀ (x : MonoidAlgebra K G) (s : S), (MulOpposite.op x) • s = s * φ x)
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M]
    (N : Type u) [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N]
    [IsScalarTower K (MonoidAlgebra K G) N] [SMulCommClass K (MonoidAlgebra K G) N]
    (k : ℕ) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    Nonempty (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) k S (TensorProduct K M N) ≃ₗ[ℤ]
      Work.ORHomAlg.Tor (R := MonoidAlgebra K G) k (TensorProduct K S M) N) :=
  torDiagSwap_aux (K := K) (G := G) (S := S) (φ := φ) (M := M) (N := N) hSright
    (diagTensorObjIso K G M N) k

end Setup

end Work.ORFinal.Chain
