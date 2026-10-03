/-
# The diagonal *right* action on `S ⊗[K] X` (the mirror of `Diagonal.lean`)

`Submission.Work.ORFlatness.Diagonal` builds the left `K[G]`-module `S ⊗[K] X` for `X` a
right `K[G]`-module, with the conjugation action
`g • (s ⊗ x) = (g·s·g⁻¹) ⊗ (x·g⁻¹)`.

Here we build the mirror: for `X` a *left* `K[G]`-module, the *right* `K[G]`-module
structure on `S ⊗[K] X` with

`(s ⊗ x)·g = (s·g) ⊗ (g⁻¹ • x)`   (`g` identified with `φ (single g 1) ∈ S`).

This is the module that Jaikin-Zapirain--Linton obtain "by symmetry" in Theorem 1.7
(the right `K[G]`-module `D_{K[G]} ⊗_K I_{K[G]}`); note that a right `K[G]`-module
structure on a type is a left `(K[G])ᵐᵒᵖ`-module structure, which is how it is encoded.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

variable (K : Type u) [CommRing K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S]
variable (φ : MonoidAlgebra K G →ₐ[K] S)
variable (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
variable [IsScalarTower K (MonoidAlgebra K G) X] [SMulCommClass K (MonoidAlgebra K G) X]

/-- The group element `g ∈ G`, viewed as an element of `S` through `φ`. -/
noncomputable def gElemR (g : G) : S := φ (MonoidAlgebra.single g (1 : K))

@[simp] theorem gElemR_one : gElemR K G S φ 1 = 1 := by
  rw [gElemR, ← MonoidAlgebra.one_def, map_one]

theorem gElemR_mul (g h : G) :
    gElemR K G S φ (g * h) = gElemR K G S φ g * gElemR K G S φ h := by
  have hsingle : (MonoidAlgebra.single g (1 : K)) * (MonoidAlgebra.single h (1 : K)) =
      MonoidAlgebra.single (g * h) (1 : K) := by
    rw [MonoidAlgebra.single_mul_single, mul_one]
  rw [gElemR, gElemR, gElemR, ← hsingle, map_mul]

/-- Right multiplication by `g` on `S`, as a `K`-linear map. -/
noncomputable def mulLinR (g : G) : S →ₗ[K] S :=
  LinearMap.mulRight K (gElemR K G S φ g)

@[simp] theorem mulLinR_apply (g : G) (s : S) :
    mulLinR K G S φ g s = s * gElemR K G S φ g := rfl

@[simp] theorem mulLinR_one : mulLinR K G S φ 1 = LinearMap.id := by
  ext s
  simp [mulLinR_apply]

theorem mulLinR_mul (g h : G) :
    mulLinR K G S φ (g * h) = (mulLinR K G S φ h).comp (mulLinR K G S φ g) := by
  ext s
  simp only [mulLinR_apply, LinearMap.comp_apply, gElemR_mul, mul_assoc]

/-- The action `x ↦ g⁻¹ • x` of `g` on `X`, as a `K`-linear map. -/
noncomputable def actLinL (g : G) : X →ₗ[K] X where
  toFun x := (MonoidAlgebra.single g⁻¹ (1 : K)) • x
  map_add' x y := smul_add _ _ _
  map_smul' k x := (smul_comm k (MonoidAlgebra.single g⁻¹ (1 : K)) x).symm

@[simp] theorem actLinL_apply (g : G) (x : X) :
    actLinL K G X g x = (MonoidAlgebra.single g⁻¹ (1 : K)) • x := rfl

@[simp] theorem actLinL_one : actLinL K G X 1 = LinearMap.id := by
  ext x
  rw [actLinL_apply, inv_one, ← MonoidAlgebra.one_def]
  simp

theorem actLinL_mul (g h : G) :
    actLinL K G X (g * h) = (actLinL K G X h).comp (actLinL K G X g) := by
  have hsingle : (MonoidAlgebra.single h⁻¹ (1 : K)) * (MonoidAlgebra.single g⁻¹ (1 : K)) =
      MonoidAlgebra.single (g * h)⁻¹ (1 : K) := by
    rw [MonoidAlgebra.single_mul_single, mul_one, mul_inv_rev]
  ext x
  rw [actLinL_apply, LinearMap.comp_apply, actLinL_apply, actLinL_apply, ← hsingle, mul_smul]

/-- The `K`-linear map `z ↦ z · g` on `S ⊗[K] X`. -/
noncomputable def diagLinR (g : G) : (S ⊗[K] X) →ₗ[K] (S ⊗[K] X) :=
  TensorProduct.map (mulLinR K G S φ g) (actLinL K G X g)

@[simp] theorem diagLinR_tmul (g : G) (s : S) (x : X) :
    diagLinR K G S φ X g (s ⊗ₜ[K] x) =
      (s * gElemR K G S φ g) ⊗ₜ[K] ((MonoidAlgebra.single g⁻¹ (1 : K)) • x) := by
  simp [diagLinR, mulLinR, actLinL]

@[simp] theorem diagLinR_one : diagLinR K G S φ X 1 = LinearMap.id := by
  rw [diagLinR, mulLinR_one, actLinL_one, TensorProduct.map_id]

/-- The diagonal right action is an anti-group-action: `z · (gh) = (z · h) · g`. -/
theorem diagLinR_mul (g h : G) :
    diagLinR K G S φ X (g * h) = (diagLinR K G S φ X h).comp (diagLinR K G S φ X g) := by
  show TensorProduct.map (mulLinR K G S φ (g * h)) (actLinL K G X (g * h)) =
    (TensorProduct.map (mulLinR K G S φ h) (actLinL K G X h)).comp
      (TensorProduct.map (mulLinR K G S φ g) (actLinL K G X g))
  rw [mulLinR_mul, actLinL_mul, TensorProduct.map_comp]

/-- The diagonal right action, as a monoid homomorphism `Gᵐᵒᵖ →* End_K(S ⊗[K] X)`. -/
noncomputable def diagMonoidHomR : Gᵐᵒᵖ →* Module.End K (S ⊗[K] X) where
  toFun g := diagLinR K G S φ X g.unop
  map_one' := by
    show diagLinR K G S φ X (1 : Gᵐᵒᵖ).unop = 1
    rw [show (1 : Gᵐᵒᵖ).unop = 1 from rfl, diagLinR_one]
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.id_apply, Module.End.one_apply]
  map_mul' g h := by
    show diagLinR K G S φ X (g * h).unop = diagLinR K G S φ X g.unop * diagLinR K G S φ X h.unop
    rw [show (g * h).unop = h.unop * g.unop from rfl, diagLinR_mul]
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.comp_apply, Module.End.mul_apply]

/-- The diagonal right action of `K[Gᵐᵒᵖ]` on `S ⊗[K] X`. -/
noncomputable def diagRingHomR : MonoidAlgebra K Gᵐᵒᵖ →ₐ[K] Module.End K (S ⊗[K] X) :=
  (MonoidAlgebra.lift K (Module.End K (S ⊗[K] X)) Gᵐᵒᵖ) (diagMonoidHomR K G S φ X)

theorem diagRingHomR_single (g : G) (c : K) :
    diagRingHomR K G S φ X (MonoidAlgebra.single (op g) c) = c • diagLinR K G S φ X g := by
  rw [diagRingHomR, MonoidAlgebra.lift_single]
  rfl

/-- The `K[Gᵐᵒᵖ]`-module structure on `S ⊗[K] X` induced by the diagonal right action. -/
noncomputable def diagModuleR : Module (MonoidAlgebra K Gᵐᵒᵖ) (S ⊗[K] X) where
  smul a z := diagRingHomR K G S φ X a z
  one_smul z := by
    show diagRingHomR K G S φ X 1 z = z
    rw [map_one, Module.End.one_apply]
  mul_smul a b z := by
    show diagRingHomR K G S φ X (a * b) z = diagRingHomR K G S φ X a (diagRingHomR K G S φ X b z)
    rw [map_mul, Module.End.mul_apply]
  smul_zero a := map_zero _
  smul_add a x y := map_add _ x y
  add_smul a b z := by
    show diagRingHomR K G S φ X (a + b) z =
      diagRingHomR K G S φ X a z + diagRingHomR K G S φ X b z
    rw [map_add]
    rfl
  zero_smul z := by
    show diagRingHomR K G S φ X 0 z = 0
    rw [map_zero]
    rfl

/-- The coefficient opposite ring equivalence (for commutative `K`). -/
noncomputable def coeffOpEquiv : Kᵐᵒᵖ ≃+* K where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_mul' x y := by simp [mul_comm]

/-- `(K[G])ᵐᵒᵖ →+* K[Gᵐᵒᵖ]`: the identity on the group basis. -/
noncomputable def opRingHom : (MonoidAlgebra K G)ᵐᵒᵖ →+* MonoidAlgebra K Gᵐᵒᵖ :=
  ((MonoidAlgebra.opRingEquiv (R := K) (M := G)).trans
    (MonoidAlgebra.mapRingEquiv Gᵐᵒᵖ (coeffOpEquiv K))).toRingHom

theorem opRingHom_op_single (g : G) (c : K) :
    opRingHom K G (op (MonoidAlgebra.single g c)) = MonoidAlgebra.single (op g) c := by
  change (MonoidAlgebra.mapRingEquiv Gᵐᵒᵖ (coeffOpEquiv K))
      ((MonoidAlgebra.opRingEquiv (R := K) (M := G)) (op (MonoidAlgebra.single g c))) =
    MonoidAlgebra.single (op g) c
  rw [MonoidAlgebra.opRingEquiv_single, MonoidAlgebra.mapRingEquiv_single]
  rfl

/-- **The diagonal right `K[G]`-module structure on `S ⊗[K] X`**:
`(s ⊗ x)·g = (s·φ g) ⊗ (g⁻¹ • x)`.  A *right* `K[G]`-module structure is encoded as a
left `(K[G])ᵐᵒᵖ`-module structure. -/
noncomputable def diagRightModule : Module ((MonoidAlgebra K G)ᵐᵒᵖ) (S ⊗[K] X) :=
  letI := diagModuleR K G S φ X
  Module.compHom (S ⊗[K] X) (opRingHom K G)

/-- The computation rule for the diagonal right action. -/
theorem diagRightModule_op_single_tmul (g : G) (s : S) (x : X) :
    letI := diagRightModule K G S φ X
    (op (MonoidAlgebra.single g (1 : K))) • (s ⊗ₜ[K] x) =
      (s * gElemR K G S φ g) ⊗ₜ[K] ((MonoidAlgebra.single g⁻¹ (1 : K)) • x) := by
  letI := diagRightModule K G S φ X
  letI := diagModuleR K G S φ X
  show diagRingHomR K G S φ X (opRingHom K G (op (MonoidAlgebra.single g (1 : K))))
      (s ⊗ₜ[K] x) = (s * gElemR K G S φ g) ⊗ₜ[K] ((MonoidAlgebra.single g⁻¹ (1 : K)) • x)
  rw [opRingHom_op_single, diagRingHomR_single]
  simp [diagLinR_tmul, gElemR]

end Work.ORFlatness
