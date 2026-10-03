/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The diagonal `K[G]`-module structure on `A ⊗[K] X`

This file provides the ingredients of Jaikin-Zapirain--Linton, Lemma 5.2 (2):
the trivial right `K[G]`-module `K`, the diagonal `K[G]`-module structure on `A ⊗[K] X`
(for `A`, `X` two `K[G]`-modules), and the resulting endofunctor
`diagTensor A : ModuleCat (K[G]) ⥤ ModuleCat (K[G])`, `X ↦ A ⊗[K] X`.

The diagonal action of `g : G` is `g • (a ⊗ x) = (g • a) ⊗ (g • x)`; it is the action
through the comultiplication of the Hopf algebra `K[G]`. It is installed as the `SMul`
instance `instDiagSMul` at high priority so that the notation `•` on `A ⊗[K] X` refers to it,
and lemmas are stated with it explicitly (`diag_smul_def`, `diag_smul_single_tmul`).
-/
import Mathlib
import Submission.Work.ORHomAlg.GroupAlgebra
import Submission.Work.ORHomAlg.Tor

/-! # The diagonal `K[G]`-module structure on `A ⊗[K] X` and the functor `X ↦ A ⊗[K] X` -/

@[expose] public section

namespace Work.ORHomAlg.JL52

open CategoryTheory
open scoped TensorProduct

universe u

variable {K : Type u} [Field K] {G : Type u} [Group G]

/-! ## The trivial right module -/

theorem augmentation_eq_lift (x : MonoidAlgebra K G) :
    Work.ORHomAlg.augmentation K G x = (MonoidAlgebra.lift K K G (1 : G →* K)) x := rfl

theorem augmentation_single (g : G) (c : K) :
    Work.ORHomAlg.augmentation K G (MonoidAlgebra.single g c) = c := by
  rw [augmentation_eq_lift, MonoidAlgebra.lift_single]
  simp

theorem augmentation_one : Work.ORHomAlg.augmentation K G (1 : MonoidAlgebra K G) = 1 := by
  rw [show (1 : MonoidAlgebra K G) = MonoidAlgebra.single (1 : G) (1 : K) from rfl,
    augmentation_single]

noncomputable instance instTrivSMul : SMul (MonoidAlgebra K G)ᵐᵒᵖ K :=
  ⟨fun a k => Work.ORHomAlg.augmentation K G (MulOpposite.unop a) * k⟩

theorem triv_smul_def (a : (MonoidAlgebra K G)ᵐᵒᵖ) (k : K) :
    a • k = Work.ORHomAlg.augmentation K G (MulOpposite.unop a) * k := rfl

noncomputable instance instTrivRightModule : Module (MonoidAlgebra K G)ᵐᵒᵖ K where
  smul := (· • ·)
  one_smul k := by
    rw [triv_smul_def, show MulOpposite.unop (1 : (MonoidAlgebra K G)ᵐᵒᵖ) = (1 : MonoidAlgebra K G)
      from rfl, augmentation_one, one_mul]
  mul_smul a b k := by
    rw [triv_smul_def, triv_smul_def, triv_smul_def, MulOpposite.unop_mul, map_mul]
    ring
  smul_zero a := by rw [triv_smul_def, mul_zero]
  smul_add a k l := by rw [triv_smul_def, triv_smul_def, triv_smul_def, mul_add]
  add_smul a b k := by
    rw [triv_smul_def, triv_smul_def, triv_smul_def, MulOpposite.unop_add, map_add, add_mul]
  zero_smul k := by rw [triv_smul_def, show MulOpposite.unop (0 : (MonoidAlgebra K G)ᵐᵒᵖ) = 0
    from rfl, map_zero, zero_mul]

@[simp]
theorem triv_op_smul_single (g : G) (k : K) :
    (MulOpposite.op (MonoidAlgebra.single g (1 : K))) • k = k := by
  rw [triv_smul_def]
  show Work.ORHomAlg.augmentation K G (MonoidAlgebra.single g (1 : K)) * k = k
  rw [augmentation_single, one_mul]

/-! ## The diagonal module structure on `A ⊗[K] X` -/

/-- The underlying `K`-linear map of the operator `a ↦ g • a`. -/
noncomputable def gLin (A : Type u) [AddCommGroup A] [Module K A] [Module (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A] (g : G) : A →ₗ[K] A where
  toFun a := MonoidAlgebra.single g (1 : K) • a
  map_add' a b := smul_add _ _ _
  map_smul' k a := (smul_comm k (MonoidAlgebra.single g (1 : K)) a).symm

@[simp]
theorem gLin_apply (A : Type u) [AddCommGroup A] [Module K A] [Module (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A] (g : G) (a : A) :
    gLin (K := K) (G := G) A g a = MonoidAlgebra.single g (1 : K) • a := rfl

theorem gLin_one (A : Type u) [AddCommGroup A] [Module K A] [Module (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A] :
    gLin (K := K) (G := G) A (1 : G) = LinearMap.id := by
  ext a
  rw [gLin_apply, show (MonoidAlgebra.single (1 : G) (1 : K)) = 1 from rfl, one_smul]
  rfl

theorem gLin_mul (A : Type u) [AddCommGroup A] [Module K A] [Module (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A] (g h : G) :
    gLin (K := K) (G := G) A (g * h) = (gLin A g).comp (gLin A h) := by
  ext a
  show MonoidAlgebra.single (g * h) (1 : K) • a
      = MonoidAlgebra.single g (1 : K) • (MonoidAlgebra.single h (1 : K) • a)
  rw [show MonoidAlgebra.single (g * h) (1 : K)
      = MonoidAlgebra.single g (1 : K) * MonoidAlgebra.single h (1 : K) by
    rw [MonoidAlgebra.single_mul_single, one_mul], mul_smul]

/-- The diagonal action of `g` on `A ⊗[K] X`. -/
noncomputable def diagElem (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] (g : G) :
    (A ⊗[K] X) →ₗ[K] (A ⊗[K] X) :=
  TensorProduct.map (gLin A g) (gLin X g)

@[simp]
theorem diagElem_tmul (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] (g : G) (a : A) (x : X) :
    diagElem (K := K) (G := G) A X g (a ⊗ₜ[K] x)
      = (MonoidAlgebra.single g (1 : K) • a) ⊗ₜ[K] (MonoidAlgebra.single g (1 : K) • x) := by
  simp [diagElem, gLin, TensorProduct.map_tmul]

theorem diagElem_one (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    diagElem (K := K) (G := G) A X 1 = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; rfl
  | tmul a x =>
    rw [diagElem_tmul,
      show (MonoidAlgebra.single (1 : G) (1 : K)) = 1 from rfl, one_smul, one_smul]
    rfl
  | add p q hp hq => rw [map_add, map_add, hp, hq]

theorem diagElem_mul (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] (g h : G) :
    diagElem (K := K) (G := G) A X (g * h)
      = (diagElem A X g).comp (diagElem A X h) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.comp_apply, diagElem_tmul, diagElem_tmul, diagElem_tmul]
    congr 1
    · rw [show MonoidAlgebra.single (g * h) (1 : K)
        = MonoidAlgebra.single g (1 : K) * MonoidAlgebra.single h (1 : K) by
          rw [MonoidAlgebra.single_mul_single, one_mul], mul_smul]
    · rw [show MonoidAlgebra.single (g * h) (1 : K)
        = MonoidAlgebra.single g (1 : K) * MonoidAlgebra.single h (1 : K) by
          rw [MonoidAlgebra.single_mul_single, one_mul], mul_smul]
  | add p q hp hq => simp only [map_add, LinearMap.comp_apply, hp, hq]

/-- The diagonal action of `G` on `A ⊗[K] X`. -/
noncomputable def diagGroupHom (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] : G →* Module.End K (A ⊗[K] X) where
  toFun := diagElem A X
  map_one' := diagElem_one A X
  map_mul' := diagElem_mul A X

/-- The diagonal action of `K[G]` on `A ⊗[K] X`, as a ring homomorphism. -/
noncomputable def diagRingHom (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    MonoidAlgebra K G →+* Module.End K (A ⊗[K] X) :=
  (MonoidAlgebra.lift K (Module.End K (A ⊗[K] X)) G (diagGroupHom A X)).toRingHom

theorem diagRingHom_single (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] (g : G) :
    diagRingHom A X (MonoidAlgebra.single g (1 : K)) = diagGroupHom A X g := by
  show (MonoidAlgebra.lift K (Module.End K (A ⊗[K] X)) G (diagGroupHom A X))
      (MonoidAlgebra.single g (1 : K)) = diagGroupHom A X g
  rw [MonoidAlgebra.lift_single]
  simp

theorem diagRingHom_smul (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] (c : K) (r : MonoidAlgebra K G) :
    diagRingHom A X (c • r) = c • diagRingHom A X r := by
  show (MonoidAlgebra.lift K (Module.End K (A ⊗[K] X)) G (diagGroupHom A X)) (c • r) = _
  rw [map_smul]
  rfl

/-- The `SMul` underlying the diagonal `K[G]`-action on `A ⊗[K] X`. -/
noncomputable instance (priority := 2000) instDiagSMul (A X : Type u) [AddCommGroup A]
    [Module K A] [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] : SMul (MonoidAlgebra K G) (A ⊗[K] X) where
  smul r z := diagRingHom A X r z

@[simp]
theorem diag_smul_def (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] (r : MonoidAlgebra K G) (z : A ⊗[K] X) :
    r • z = diagRingHom A X r z := rfl

/-- The diagonal `K[G]`-module structure on `A ⊗[K] X`. -/
noncomputable instance instDiagModule (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    Module (MonoidAlgebra K G) (A ⊗[K] X) where
  smul := (instDiagSMul A X).smul
  one_smul z := by rw [diag_smul_def, map_one] <;> rfl
  mul_smul r s z := by rw [diag_smul_def, diag_smul_def, diag_smul_def, map_mul] <;> rfl
  smul_zero r := by rw [diag_smul_def, map_zero] <;> rfl
  smul_add r z w := by rw [diag_smul_def, map_add] <;> rfl
  add_smul r s z := by rw [diag_smul_def, diag_smul_def, diag_smul_def, map_add] <;> rfl
  zero_smul z := by rw [diag_smul_def, map_zero] <;> rfl

@[simp]
theorem diag_smul_single_tmul (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] (g : G) (a : A) (x : X) :
    (MonoidAlgebra.single g (1 : K)) • (a ⊗ₜ[K] x) =
      (MonoidAlgebra.single g (1 : K) • a) ⊗ₜ[K] (MonoidAlgebra.single g (1 : K) • x) := by
  rw [diag_smul_def, diagRingHom_single]
  exact diagElem_tmul A X g a x

/-! ## The canonical `K`-structure on objects of `ModuleCat (K[G])` -/

/-- The `K`-action on an object of `ModuleCat (MonoidAlgebra K G)`. -/
noncomputable instance instSMulCatK (X : ModuleCat.{u} (MonoidAlgebra K G)) : SMul K ↥X :=
  ⟨fun c x => algebraMap K (MonoidAlgebra K G) c • x⟩

theorem smulCatK_def (X : ModuleCat.{u} (MonoidAlgebra K G)) (c : K) (x : ↥X) :
    c • x = algebraMap K (MonoidAlgebra K G) c • x := rfl

noncomputable instance instModuleCatK (X : ModuleCat.{u} (MonoidAlgebra K G)) : Module K ↥X where
  smul := (instSMulCatK X).smul
  one_smul x := by simp only [smulCatK_def, map_one, one_smul]
  mul_smul c d x := by simp only [smulCatK_def, map_mul, mul_smul]
  smul_zero c := by simp only [smulCatK_def, smul_zero]
  smul_add c x y := by simp only [smulCatK_def, smul_add]
  add_smul c d x := by simp only [smulCatK_def, map_add, add_smul]
  zero_smul x := by simp only [smulCatK_def, map_zero, zero_smul]

instance instIsScalarTowerCatK (X : ModuleCat.{u} (MonoidAlgebra K G)) :
    IsScalarTower K (MonoidAlgebra K G) ↥X where
  smul_assoc c r x := by
    rw [Algebra.smul_def, mul_smul]
    rfl

/-! ## The functor `X ↦ A ⊗[K] X` -/

/-- Restriction of scalars of a `K[G]`-linear map along `K → K[G]`. -/
noncomputable def restrictK {X Y : Type u} [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [AddCommGroup Y] [Module K Y]
    [Module (MonoidAlgebra K G) Y] [IsScalarTower K (MonoidAlgebra K G) Y]
    (f : X →ₗ[MonoidAlgebra K G] Y) : X →ₗ[K] Y where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    have h1 : (algebraMap K (MonoidAlgebra K G) c) • x = c • x := by
      rw [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc, one_smul]
    have h2 : (algebraMap K (MonoidAlgebra K G) c) • f x = c • f x := by
      rw [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc, one_smul]
    rw [← h1, f.map_smul, h2]
    rfl

@[simp]
theorem restrictK_apply {X Y : Type u} [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [AddCommGroup Y] [Module K Y]
    [Module (MonoidAlgebra K G) Y] [IsScalarTower K (MonoidAlgebra K G) Y] (f : X →ₗ[MonoidAlgebra K G] Y) (x : X) :
    restrictK (G := G) f x = f x := rfl

theorem restrictK_id {X : Type u} [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X] :
    restrictK (G := G) (LinearMap.id : X →ₗ[MonoidAlgebra K G] X) = LinearMap.id := rfl

theorem restrictK_comp {X Y Z : Type u} [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [AddCommGroup Y] [Module K Y]
    [Module (MonoidAlgebra K G) Y] [IsScalarTower K (MonoidAlgebra K G) Y]
    [AddCommGroup Z] [Module K Z]
    [Module (MonoidAlgebra K G) Z] [IsScalarTower K (MonoidAlgebra K G) Z] (f : Y →ₗ[MonoidAlgebra K G] Z)
    (g : X →ₗ[MonoidAlgebra K G] Y) :
    restrictK (G := G) (f.comp g) = (restrictK f).comp (restrictK g) := rfl

theorem restrictK_add {X Y : Type u} [AddCommGroup X] [Module K X]
    [Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [AddCommGroup Y] [Module K Y]
    [Module (MonoidAlgebra K G) Y] [IsScalarTower K (MonoidAlgebra K G) Y] (f g : X →ₗ[MonoidAlgebra K G] Y) :
    restrictK (G := G) (f + g) = restrictK f + restrictK g := rfl

/-- The `K`-linear map `id_A ⊗ f` is `K[G]`-linear for the diagonal structures. -/
theorem diagTensorMap_smul (A : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    {X Y : Type u} [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    [AddCommGroup Y] [Module K Y] [Module (MonoidAlgebra K G) Y]
    [SMulCommClass K (MonoidAlgebra K G) Y] [IsScalarTower K (MonoidAlgebra K G) Y]
    (f : X →ₗ[MonoidAlgebra K G] Y) (r : MonoidAlgebra K G) (z : A ⊗[K] X) :
    TensorProduct.map (LinearMap.id : A →ₗ[K] A) (restrictK f) (r • z) =
      r • TensorProduct.map (LinearMap.id : A →ₗ[K] A) (restrictK f) z := by
  induction r using MonoidAlgebra.induction_on with
  | of m =>
      rw [MonoidAlgebra.of_apply, diag_smul_def, diag_smul_def, diagRingHom_single, diagRingHom_single]
      change TensorProduct.map (LinearMap.id : A →ₗ[K] A) (restrictK f) (diagElem A X m z) =
        diagElem A Y m (TensorProduct.map (LinearMap.id : A →ₗ[K] A) (restrictK f) z)
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
          rw [diagElem_tmul, TensorProduct.map_tmul, LinearMap.id_apply, restrictK_apply]
          rw [TensorProduct.map_tmul, LinearMap.id_apply, restrictK_apply, diagElem_tmul]
          rw [f.map_smul]
      | add p q hp hq => simp only [map_add, hp, hq]
  | add r s hr hs => rw [add_smul, map_add, hr, hs, add_smul]
  | smul c r hr =>
      change TensorProduct.map (LinearMap.id : A →ₗ[K] A) (restrictK f)
          (diagRingHom A X (c • r) z) =
        diagRingHom A Y (c • r)
          (TensorProduct.map (LinearMap.id : A →ₗ[K] A) (restrictK f) z)
      rw [diagRingHom_smul, diagRingHom_smul, LinearMap.smul_apply, LinearMap.smul_apply,
        LinearMap.map_smul, ← diag_smul_def, ← diag_smul_def, hr]

/-- The functor `X ↦ A ⊗[K] X` with the diagonal `K[G]`-module structure. -/
noncomputable def diagTensor (A : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    ModuleCat.{u} (MonoidAlgebra K G) ⥤ ModuleCat.{u} (MonoidAlgebra K G) where
  obj X := ModuleCat.of (MonoidAlgebra K G) (A ⊗[K] ↥X)
  map {X Y} f := ModuleCat.ofHom
    { toFun := LinearMap.lTensor A (restrictK f.hom)
      map_add' := map_add _
      map_smul' := fun r z => diagTensorMap_smul A f.hom r z }
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (LinearMap.lTensor A (restrictK (LinearMap.id : ↥X →ₗ[MonoidAlgebra K G] ↥X))) z = z
    rw [restrictK_id, LinearMap.lTensor_id] <;> rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (LinearMap.lTensor A (restrictK (g.hom.comp f.hom))) z =
      ((LinearMap.lTensor A (restrictK g.hom)).comp (LinearMap.lTensor A (restrictK f.hom))) z
    rw [restrictK_comp, LinearMap.lTensor_comp] <;> rfl
instance diagTensor_additive (A : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    (diagTensor (K := K) (G := G) A).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (LinearMap.lTensor A (restrictK (f.hom + g.hom))) z =
      ((LinearMap.lTensor A (restrictK f.hom)) + (LinearMap.lTensor A (restrictK g.hom))) z
    rw [restrictK_add, LinearMap.lTensor_add] <;> rfl

end Work.ORHomAlg.JL52
