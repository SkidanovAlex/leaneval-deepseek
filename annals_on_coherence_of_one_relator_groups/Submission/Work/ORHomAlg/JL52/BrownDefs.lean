/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Jaikin-Zapirain--Linton, Lemma 5.2 (2): the Brown comparison isomorphism

This file develops the ingredients of the natural isomorphism of functors
`X ↦ A ⊠[K[G]] X  ≅  X ↦ K ⊠[K[G]] (A ⊗[K] X)`
of Jaikin-Zapirain--Linton, Lemma 5.2 (2) (cited there as Brown, *Cohomology of Groups*,
Proposition III.2.2).  Here `A` is simultaneously a left and a right `K[G]`-module whose left
`K[G]`-action is the antipode-twist of the right one (`hA` below), so that `A` is "simultaneously
`L` and `L*`".

The comparison maps are
* `alpha : A ⊠[K[G]] X → K ⊠[K[G]] (A ⊗[K] X)`, induced by `a ⊠ x ↦ 1 ⊠ (a ⊗ x)`;
* `beta  : K ⊠[K[G]] (A ⊗[K] X) → A ⊠[K[G]] X`, induced by `k ⊠ (a ⊗ x) ↦ k • (a ⊠ x)`;
and the main theorems `alpha_beta`/`beta_alpha` show that they are mutually inverse.
-/
import Mathlib
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs
import Submission.Work.ORHomAlg.JL52.isScalarTowerDiag
import Submission.Work.ORHomAlg.JL52.smulCommClassDiag

@[expose] public section

namespace Work.ORHomAlg.JL52

open CategoryTheory
open scoped TensorProduct
open Work.ORHomAlg

universe u

variable {K : Type u} [Field K] {G : Type u} [Group G]

/-! ## The `K`-scalar action and the trivial right `K[G]`-action on `K` commute -/

/-- The `K`-scalar action and the trivial right `K[G]`-action on `K` commute.  This makes
`K ⊠[K[G]] W` a `K`-module via the left factor `K`. -/
instance instSMulCommClassTrivRight : SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ K where
  smul_comm c r k := by
    rw [triv_smul_def]
    show (c : K) * (augmentation K G (MulOpposite.unop r) * k) =
      augmentation K G (MulOpposite.unop r) * (c * k)
    ring

/-- `op (single 1 k) • x = k * x` for the trivial right action of `K[G]` on `K`. -/
@[simp]
theorem triv_op_smul_single_one (k x : K) :
    (MulOpposite.op (MonoidAlgebra.single (1 : G) k)) • x = k * x := by
  rw [triv_smul_def, MulOpposite.unop_op, augmentation_single]

/-- `algebraMap K (K[G]) k = single 1 k`. -/
theorem algebraMap_monoidAlgebra_eq_single (k : K) :
    algebraMap K (MonoidAlgebra K G) k = MonoidAlgebra.single (1 : G) k := by
  rw [Algebra.algebraMap_eq_smul_one]
  show k • (1 : MonoidAlgebra K G) = MonoidAlgebra.single 1 k
  rw [show (1 : MonoidAlgebra K G) = MonoidAlgebra.single (1 : G) (1 : K) from rfl,
    MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- `op (algebraMap K (K[G]) k) • x = k * x` for the trivial right action on `K`. -/
@[simp]
theorem triv_op_smul_algebraMap (k x : K) :
    (MulOpposite.op (algebraMap K (MonoidAlgebra K G) k)) • x = k * x := by
  rw [algebraMap_monoidAlgebra_eq_single, triv_op_smul_single_one]

/-! ## The main algebraic inputs -/

section Key

variable {A : Type u} [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [IsScalarTower K (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A]
    [Module (MonoidAlgebra K G)ᵐᵒᵖ A] [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ A]
    [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ A]

/-- The direction of `hA` that we use: the right action of `single g 1` is the left action of
`single g⁻¹ 1`. -/
theorem hA_op (hA : ∀ (g : G) (a : A), (MonoidAlgebra.single g (1 : K)) • a =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • a) (g : G) (a : A) :
    MulOpposite.op (MonoidAlgebra.single g (1 : K)) • a =
      MonoidAlgebra.single g⁻¹ (1 : K) • a := by
  have h := hA g⁻¹ a
  rw [inv_inv] at h
  exact h.symm

/-- `k • w = (algebraMap K (K[G]) k) • w` for the diagonal `K[G]`-structure on `A ⊗[K] X`. -/
theorem diag_algebraMap_smul (X : ModuleCat.{u} (MonoidAlgebra K G)) (k : K)
    (w : A ⊗[K] ↥X) : (algebraMap K (MonoidAlgebra K G) k) • w = k • w := by
  have h : diagRingHom A ↥X (algebraMap K (MonoidAlgebra K G) k)
      = k • (1 : Module.End K (A ⊗[K] ↥X)) := by
    rw [Algebra.algebraMap_eq_smul_one, diagRingHom_smul, map_one]
  rw [diag_smul_def, h]
  show (k • (1 : Module.End K (A ⊗[K] ↥X))) w = k • w
  rw [LinearMap.smul_apply, Module.End.one_apply]

/-- The `K`-scalar action on the first factor of `K ⊠[K[G]] W`: `k ⊠ w ↦ (k k') ⊠ w`. -/
theorem tmul_one_smul (X : ModuleCat.{u} (MonoidAlgebra K G)) (k : K) (w : A ⊗[K] ↥X) :
    BalancedTensor.tmul (MonoidAlgebra K G) (1 : K) (k • w) =
      k • BalancedTensor.tmul (MonoidAlgebra K G) (1 : K) w := by
  rw [← diag_algebraMap_smul X k w,
    ← BalancedTensor.tmul_smul (R := MonoidAlgebra K G) (M := K) (N := A ⊗[K] ↥X)
      (m := (1 : K)) (r := algebraMap K (MonoidAlgebra K G) k) (n := w),
    triv_op_smul_algebraMap, mul_one,
    BalancedTensor.smul_tmul (R := MonoidAlgebra K G) (M := K) (N := A ⊗[K] ↥X)
      (s := k) (m := (1 : K)) (n := w)]
  rw [smul_eq_mul, mul_one]

/-- The comparison relation, for a single generator `single g 1` of `K[G]`. -/
theorem tmul_one_op_single (hA : ∀ (g : G) (a : A), (MonoidAlgebra.single g (1 : K)) • a =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • a)
    (X : ModuleCat.{u} (MonoidAlgebra K G)) (g : G) (a : A) (x : ↥X) :
    BalancedTensor.tmul (MonoidAlgebra K G) (1 : K)
        ((MulOpposite.op (MonoidAlgebra.single g (1 : K)) • a) ⊗ₜ[K] x) =
      BalancedTensor.tmul (MonoidAlgebra K G) (1 : K)
        (a ⊗ₜ[K] ((MonoidAlgebra.single g (1 : K)) • x)) := by
  have h1 : MulOpposite.op (MonoidAlgebra.single g (1 : K)) • a =
      MonoidAlgebra.single g⁻¹ (1 : K) • a := hA_op hA g a
  have h2 : (MonoidAlgebra.single g⁻¹ (1 : K) • a) ⊗ₜ[K] x =
      (MonoidAlgebra.single g⁻¹ (1 : K)) •
        (a ⊗ₜ[K] ((MonoidAlgebra.single g (1 : K)) • x)) := by
    rw [diag_smul_single_tmul]
    congr 1
    rw [← mul_smul, show MonoidAlgebra.single g⁻¹ (1 : K) * MonoidAlgebra.single g (1 : K)
        = 1 by rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, mul_one]; rfl, one_smul]
  rw [h1, h2,
    ← BalancedTensor.tmul_smul (R := MonoidAlgebra K G) (M := K) (N := A ⊗[K] ↥X)
      (m := (1 : K)) (r := MonoidAlgebra.single g⁻¹ (1 : K))
      (n := a ⊗ₜ[K] ((MonoidAlgebra.single g (1 : K)) • x)),
    triv_op_smul_single]

/-- The comparison relation for an arbitrary `r : K[G]`:
`1 ⊠ ((a·r) ⊗ x) = 1 ⊠ (a ⊗ (r·x))`.  This is what makes `a ⊠ x ↦ 1 ⊠ (a ⊗ x)` well defined. -/
theorem tmul_one_op_smul (hA : ∀ (g : G) (a : A), (MonoidAlgebra.single g (1 : K)) • a =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • a)
    (X : ModuleCat.{u} (MonoidAlgebra K G)) (r : MonoidAlgebra K G) (a : A) (x : ↥X) :
    BalancedTensor.tmul (MonoidAlgebra K G) (1 : K) ((MulOpposite.op r • a) ⊗ₜ[K] x) =
      BalancedTensor.tmul (MonoidAlgebra K G) (1 : K) (a ⊗ₜ[K] (r • x)) := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
      rw [MonoidAlgebra.of_apply]
      exact tmul_one_op_single hA X g a x
  | add r s hr hs =>
      rw [MulOpposite.op_add, add_smul, TensorProduct.add_tmul, BalancedTensor.tmul_add',
        add_smul, TensorProduct.tmul_add, BalancedTensor.tmul_add', hr, hs]
  | smul c r hr =>
      rw [MulOpposite.op_smul, IsScalarTower.smul_assoc, ← TensorProduct.smul_tmul',
        IsScalarTower.smul_assoc, TensorProduct.tmul_smul, tmul_one_smul, tmul_one_smul, hr]

end Key

/-! ## The comparison maps -/

section Defs

variable {A : Type u} [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [IsScalarTower K (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A]
    [Module (MonoidAlgebra K G)ᵐᵒᵖ A] [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ A]
    [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ A]

/-- The diagonal `K[G]`-action on `A ⊗[K] X` is a scalar tower over `K`. -/
instance instIsScalarTowerDiag (X : ModuleCat.{u} (MonoidAlgebra K G)) :
    IsScalarTower K (MonoidAlgebra K G) (A ⊗[K] ↥X) :=
  isScalarTowerDiag K G A ↥X

/-- `r • (z + w) = r • z + r • w` for the diagonal action on `A ⊗[K] X`. -/
theorem diag_smul_add (X : ModuleCat.{u} (MonoidAlgebra K G)) (r : MonoidAlgebra K G)
    (z w : A ⊗[K] ↥X) : r • (z + w) = r • z + r • w := by
  rw [diag_smul_def, map_add, ← diag_smul_def, ← diag_smul_def]

/-- `(r + s) • z = r • z + s • z` for the diagonal action on `A ⊗[K] X`. -/
theorem diag_add_smul (X : ModuleCat.{u} (MonoidAlgebra K G)) (r s : MonoidAlgebra K G)
    (z : A ⊗[K] ↥X) : (r + s) • z = r • z + s • z := by
  rw [diag_smul_def, map_add, LinearMap.add_apply, ← diag_smul_def, ← diag_smul_def]

/-- `op (algebraMap K (K[G]) k) • a = k • a` for the right action of `K[G]` on `A`. -/
theorem op_algebraMap_smul (k : K) (a : A) :
    MulOpposite.op (algebraMap K (MonoidAlgebra K G) k) • a = k • a := by
  rw [Algebra.algebraMap_eq_smul_one, MulOpposite.op_smul, MulOpposite.op_one,
    IsScalarTower.smul_assoc, one_smul]

/-- `augmentation K G (algebraMap K (K[G]) k) = k`. -/
@[simp]
theorem augmentation_algebraMap (k : K) :
    augmentation K G (algebraMap K (MonoidAlgebra K G) k) = k := by
  rw [algebraMap_monoidAlgebra_eq_single, augmentation_single]

/-- The `K`-bilinear map underlying `gamma`: `(a, x) ↦ a ⊠ x`. -/
noncomputable def gammaBilin (X : ModuleCat.{u} (MonoidAlgebra K G)) :
    A →ₗ[K] (↥X →ₗ[K] BalancedTensor (MonoidAlgebra K G) A ↥X) where
  toFun a :=
    { toFun := fun x => BalancedTensor.tmul (MonoidAlgebra K G) a x
      map_add' := fun x y => BalancedTensor.tmul_add' a x y
      map_smul' := fun k x => by
        show BalancedTensor.tmul (MonoidAlgebra K G) a (k • x) =
          k • BalancedTensor.tmul (MonoidAlgebra K G) a x
        rw [show k • BalancedTensor.tmul (MonoidAlgebra K G) a x =
            BalancedTensor.tmul (MonoidAlgebra K G) (k • a) x from
          BalancedTensor.smul_tmul (R := MonoidAlgebra K G) (M := A) (N := ↥X) k a x,
          ← op_algebraMap_smul (K := K) (G := G) k a,
          BalancedTensor.tmul_smul (R := MonoidAlgebra K G) (M := A) (N := ↥X)
            (m := a) (r := algebraMap K (MonoidAlgebra K G) k) (n := x),
          ← smulCatK_def X k x] }
  map_add' a b := by
    apply LinearMap.ext
    intro x
    exact BalancedTensor.tmul_add (R := MonoidAlgebra K G) a b x
  map_smul' k a := by
    apply LinearMap.ext
    intro x
    exact (BalancedTensor.smul_tmul (R := MonoidAlgebra K G) (M := A) (N := ↥X) k a x).symm

/-- The `K`-linear map `W = A ⊗[K] X → A ⊠[K[G]] X`, `a ⊗ x ↦ a ⊠ x`. -/
noncomputable def gamma (X : ModuleCat.{u} (MonoidAlgebra K G)) :
    (A ⊗[K] ↥X) →ₗ[K] BalancedTensor (MonoidAlgebra K G) A ↥X :=
  TensorProduct.lift (gammaBilin X)

@[simp]
theorem gamma_tmul (X : ModuleCat.{u} (MonoidAlgebra K G)) (a : A) (x : ↥X) :
    gamma (K := K) (G := G) X (a ⊗ₜ[K] x) =
      BalancedTensor.tmul (MonoidAlgebra K G) a x := by
  show TensorProduct.lift (gammaBilin X) (a ⊗ₜ[K] x) =
    BalancedTensor.tmul (MonoidAlgebra K G) a x
  rw [TensorProduct.lift.tmul]
  rfl

/-- `lam`: the map `W = A ⊗[K] X → K ⊠[K[G]] W`, `w ↦ 1 ⊠ w`. -/
noncomputable def lam (X : ModuleCat.{u} (MonoidAlgebra K G)) :
    (A ⊗[K] ↥X) →ₗ[ℤ] BalancedTensor (MonoidAlgebra K G) K (A ⊗[K] ↥X) :=
  (BalancedTensor.tmulAddHom (MonoidAlgebra K G) (1 : K)).toIntLinearMap

@[simp]
theorem lam_apply (X : ModuleCat.{u} (MonoidAlgebra K G)) (w : A ⊗[K] ↥X) :
    lam (K := K) (G := G) X w = BalancedTensor.tmul (MonoidAlgebra K G) (1 : K) w := rfl

/-- `gamma (r • w) = augmentation r • gamma w`: the diagonal action of `K[G]` on `A ⊗[K] X`
descends to the `K`-coinvariants `A ⊠[K[G]] X`. -/
theorem gamma_smul (hA : ∀ (g : G) (a : A), (MonoidAlgebra.single g (1 : K)) • a =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • a)
    (X : ModuleCat.{u} (MonoidAlgebra K G)) (r : MonoidAlgebra K G) (w : A ⊗[K] ↥X) :
    gamma (K := K) (G := G) X (r • w) =
      augmentation K G r • gamma (K := K) (G := G) X w := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
      rw [MonoidAlgebra.of_apply]
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
          rw [diag_smul_single_tmul, gamma_tmul, gamma_tmul, augmentation_single, one_smul,
            hA g a,
            BalancedTensor.tmul_smul (R := MonoidAlgebra K G) (M := A) (N := ↥X)
              (m := a) (r := MonoidAlgebra.single g⁻¹ (1 : K))
              (n := MonoidAlgebra.single g (1 : K) • x)]
          congr 1
          rw [← mul_smul, show MonoidAlgebra.single g⁻¹ (1 : K) * MonoidAlgebra.single g (1 : K)
            = 1 by rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, mul_one]; rfl, one_smul]
      | add p q hp hq =>
          rw [diag_smul_add, map_add, hp, hq, map_add, smul_add]
  | add r s hr hs =>
      rw [diag_add_smul, map_add, hr, hs, map_add, add_smul]
  | smul c r hr =>
      rw [IsScalarTower.smul_assoc, map_smul, hr,
        show augmentation K G (c • r) = c * augmentation K G r by
          rw [Algebra.smul_def, map_mul, augmentation_algebraMap],
        smul_smul]

/-- `alpha` is induced by `a ⊠ x ↦ 1 ⊠ (a ⊗ x)`. -/
noncomputable def alpha (hA : ∀ (g : G) (a : A), (MonoidAlgebra.single g (1 : K)) • a =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • a)
    (X : ModuleCat.{u} (MonoidAlgebra K G)) :
    BalancedTensor (MonoidAlgebra K G) A ↥X →ₗ[ℤ]
      BalancedTensor (MonoidAlgebra K G) K (A ⊗[K] ↥X) :=
  BalancedTensor.lift
    { toFun := fun a =>
        (BalancedTensor.tmulAddHom (MonoidAlgebra K G) (1 : K)).comp
          { toFun := fun x => a ⊗ₜ[K] x
            map_zero' := by simp
            map_add' := fun x y => TensorProduct.tmul_add a x y }
      map_zero' := by
        apply AddMonoidHom.ext
        intro x
        show BalancedTensor.tmul (MonoidAlgebra K G) (1 : K) ((0 : A) ⊗ₜ[K] x) = 0
        rw [TensorProduct.zero_tmul]
        exact BalancedTensor.zero_tmul (M := K) (R := MonoidAlgebra K G) (1 : K)
      map_add' := by
        intro a b
        apply AddMonoidHom.ext
        intro x
        show BalancedTensor.tmul (MonoidAlgebra K G) (1 : K) ((a + b) ⊗ₜ[K] x) =
          BalancedTensor.tmul (MonoidAlgebra K G) (1 : K) (a ⊗ₜ[K] x) +
            BalancedTensor.tmul (MonoidAlgebra K G) (1 : K) (b ⊗ₜ[K] x)
        rw [TensorProduct.add_tmul, BalancedTensor.tmul_add'] }
    (fun a r x => tmul_one_op_smul hA X r a x)

@[simp]
theorem alpha_tmul (hA : ∀ (g : G) (a : A), (MonoidAlgebra.single g (1 : K)) • a =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • a)
    (X : ModuleCat.{u} (MonoidAlgebra K G)) (a : A) (x : ↥X) :
    alpha hA X (BalancedTensor.tmul (MonoidAlgebra K G) a x) =
      BalancedTensor.tmul (MonoidAlgebra K G) (1 : K) (a ⊗ₜ[K] x) :=
  BalancedTensor.lift_tmul _ _ a x

/-- `beta` is induced by `k ⊠ (a ⊗ x) ↦ k • (a ⊠ x)`. -/
noncomputable def beta (hA : ∀ (g : G) (a : A), (MonoidAlgebra.single g (1 : K)) • a =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • a)
    (X : ModuleCat.{u} (MonoidAlgebra K G)) :
    BalancedTensor (MonoidAlgebra K G) K (A ⊗[K] ↥X) →ₗ[ℤ]
      BalancedTensor (MonoidAlgebra K G) A ↥X :=
  BalancedTensor.lift
    { toFun := fun k =>
        { toFun := fun w => k • gamma (K := K) (G := G) X w
          map_zero' := by rw [map_zero, smul_zero]
          map_add' := fun w w' => by rw [map_add, smul_add] }
      map_zero' := by
        apply AddMonoidHom.ext
        intro w
        show (0 : K) • gamma (K := K) (G := G) X w = 0
        rw [zero_smul]
      map_add' := by
        intro k l
        apply AddMonoidHom.ext
        intro w
        show (k + l) • gamma (K := K) (G := G) X w =
          k • gamma (K := K) (G := G) X w + l • gamma (K := K) (G := G) X w
        rw [add_smul] }
    (fun k r w => by
      show (MulOpposite.op r • k) • gamma (K := K) (G := G) X w =
        k • gamma (K := K) (G := G) X (r • w)
      rw [triv_smul_def, MulOpposite.unop_op, gamma_smul hA X r w, smul_smul,
        mul_comm (augmentation K G r) k])

@[simp]
theorem beta_tmul (hA : ∀ (g : G) (a : A), (MonoidAlgebra.single g (1 : K)) • a =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • a)
    (X : ModuleCat.{u} (MonoidAlgebra K G)) (k : K) (w : A ⊗[K] ↥X) :
    beta hA X (BalancedTensor.tmul (MonoidAlgebra K G) k w) =
      k • gamma (K := K) (G := G) X w :=
  BalancedTensor.lift_tmul _ _ k w

end Defs

/-! ## `alpha` and `beta` are mutually inverse -/

section Iso

variable {A : Type u} [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [IsScalarTower K (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A]
    [Module (MonoidAlgebra K G)ᵐᵒᵖ A] [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ A]
    [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ A]

variable (hA : ∀ (g : G) (a : A), (MonoidAlgebra.single g (1 : K)) • a =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • a)

/-- `alpha` is `K`-linear. -/
theorem alpha_smul (X : ModuleCat.{u} (MonoidAlgebra K G)) (c : K)
    (z : BalancedTensor (MonoidAlgebra K G) A ↥X) :
    alpha hA X (c • z) = c • alpha hA X z := by
  induction z using BalancedTensor.induction_on with
  | H0 => rw [smul_zero, map_zero, smul_zero]
  | Hadd p q hp hq => rw [smul_add, map_add, map_add, hp, hq, smul_add]
  | Htmul a x =>
      rw [BalancedTensor.smul_tmul, alpha_tmul, alpha_tmul,
        ← tmul_one_smul (K := K) (G := G) X c (a ⊗ₜ[K] x), TensorProduct.smul_tmul']

/-- `alpha ∘ gamma = lam`. -/
theorem alpha_gamma (X : ModuleCat.{u} (MonoidAlgebra K G)) (w : A ⊗[K] ↥X) :
    alpha hA X (gamma (K := K) (G := G) X w) = lam (K := K) (G := G) X w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a x => rw [gamma_tmul, alpha_tmul, lam_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- `beta ∘ alpha = id`. -/
theorem beta_alpha (X : ModuleCat.{u} (MonoidAlgebra K G))
    (z : BalancedTensor (MonoidAlgebra K G) A ↥X) : beta hA X (alpha hA X z) = z := by
  induction z using BalancedTensor.induction_on with
  | H0 => rw [map_zero, map_zero]
  | Hadd p q hp hq => rw [map_add, map_add, hp, hq]
  | Htmul a x => rw [alpha_tmul, beta_tmul, one_smul, gamma_tmul]

/-- `alpha ∘ beta = id`. -/
theorem alpha_beta (X : ModuleCat.{u} (MonoidAlgebra K G))
    (z : BalancedTensor (MonoidAlgebra K G) K (A ⊗[K] ↥X)) : alpha hA X (beta hA X z) = z := by
  induction z using BalancedTensor.induction_on with
  | H0 => rw [map_zero, map_zero]
  | Hadd p q hp hq => rw [map_add, map_add, hp, hq]
  | Htmul k w =>
      rw [beta_tmul, alpha_smul, alpha_gamma, lam_apply,
        BalancedTensor.smul_tmul (R := MonoidAlgebra K G) (M := K) (N := A ⊗[K] ↥X)
          (s := k) (m := (1 : K)) (n := w), smul_eq_mul, mul_one]

end Iso

/-! ## The functor-level isomorphism -/

section Functor

variable {A : Type u} [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [IsScalarTower K (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A]
    [Module (MonoidAlgebra K G)ᵐᵒᵖ A] [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ A]
    [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ A]

variable (hA : ∀ (g : G) (a : A), (MonoidAlgebra.single g (1 : K)) • a =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • a)

/-- The componentwise `ℤ`-linear equivalence `A ⊠[K[G]] X ≃ K ⊠[K[G]] (A ⊗[K] X)`. -/
noncomputable def brownLinearEquiv (X : ModuleCat.{u} (MonoidAlgebra K G)) :
    BalancedTensor (MonoidAlgebra K G) A ↥X ≃ₗ[ℤ]
      BalancedTensor (MonoidAlgebra K G) K (A ⊗[K] ↥X) where
  toFun := alpha hA X
  invFun := beta hA X
  left_inv := fun z => beta_alpha hA X z
  right_inv := fun z => alpha_beta hA X z
  map_add' := fun z w => (alpha hA X).map_add z w
  map_smul' := fun n z => (alpha hA X).map_smul n z

/-- The component of the natural isomorphism at `X`. -/
noncomputable def brownIsoComponent (X : ModuleCat.{u} (MonoidAlgebra K G)) :
    (tensorLeftFunctor (R := MonoidAlgebra K G) A).obj X ≅
      ((diagTensor (K := K) (G := G) A) ⋙
        tensorLeftFunctor (R := MonoidAlgebra K G) K).obj X :=
  LinearEquiv.toModuleIso (brownLinearEquiv (K := K) (G := G) hA X)

/-- The diagonal-tensor functor on a pure tensor. -/
@[simp]
theorem diagTensor_map_tmul {X Y : ModuleCat.{u} (MonoidAlgebra K G)} (f : X ⟶ Y)
    (a : A) (x : ↥X) :
    ((diagTensor (K := K) (G := G) A).map f).hom (a ⊗ₜ[K] x) = a ⊗ₜ[K] f.hom x := by
  show LinearMap.lTensor A (restrictK (G := G) f.hom) (a ⊗ₜ[K] x) = a ⊗ₜ[K] f.hom x
  rw [LinearMap.lTensor_tmul, restrictK_apply]

/-- The `tensorLeftFunctor` on a pure tensor. -/
@[simp]
theorem tensorLeftFunctor_map_tmul {R : Type u} [Ring R] {M : Type u} [AddCommGroup M]
    [Module Rᵐᵒᵖ M] {N N' : ModuleCat.{u} R} (g : N ⟶ N') (m : M) (n : ↥N) :
    ((tensorLeftFunctor (R := R) M).map g).hom (BalancedTensor.tmul R m n) =
      BalancedTensor.tmul R m (g.hom n) := by
  show BalancedTensor.lTensor (M := M) g.hom (BalancedTensor.tmul R m n) =
    BalancedTensor.tmul R m (g.hom n)
  rw [BalancedTensor.lTensor_tmul]

/-- `alpha` intertwines the two actions of `f`; this is the naturality square. -/
theorem alpha_lTensor {X Y : ModuleCat.{u} (MonoidAlgebra K G)} (f : X ⟶ Y)
    (z : BalancedTensor (MonoidAlgebra K G) A ↥X) :
    alpha hA Y (BalancedTensor.lTensor (M := A) f.hom z) =
      ((tensorLeftFunctor (R := MonoidAlgebra K G) K).map
        ((diagTensor (K := K) (G := G) A).map f)).hom (alpha hA X z) := by
  induction z using BalancedTensor.induction_on with
  | H0 =>
      show (0 : BalancedTensor (MonoidAlgebra K G) K (A ⊗[K] ↥Y)) = 0
      rfl
  | Hadd p q hp hq =>
      erw [map_add, map_add, map_add, hp, hq, map_add]
      rfl
  | Htmul a x =>
      erw [BalancedTensor.lTensor_tmul, alpha_tmul]

/-- Naturality of the comparison map `alpha`. -/
theorem alpha_naturality {X Y : ModuleCat.{u} (MonoidAlgebra K G)} (f : X ⟶ Y) :
    (tensorLeftFunctor (R := MonoidAlgebra K G) A).map f ≫ (brownIsoComponent hA Y).hom =
      (brownIsoComponent hA X).hom ≫
        ((diagTensor (K := K) (G := G) A) ⋙
          tensorLeftFunctor (R := MonoidAlgebra K G) K).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact alpha_lTensor hA f z

/-- Jaikin-Zapirain--Linton, Lemma 5.2 (2), functorial form. -/
noncomputable def brownNatIso :
    (tensorLeftFunctor (R := MonoidAlgebra K G) A) ≅
      ((diagTensor (K := K) (G := G) A) ⋙
        tensorLeftFunctor (R := MonoidAlgebra K G) K) :=
  NatIso.ofComponents (fun X => brownIsoComponent hA X) (fun f => alpha_naturality hA f)

end Functor

end Work.ORHomAlg.JL52
