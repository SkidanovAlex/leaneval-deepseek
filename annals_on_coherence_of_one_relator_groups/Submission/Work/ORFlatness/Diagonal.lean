/-
# The diagonal ("conjugation") action on `S ⊗[K] X`

Let `K` be a commutative ring, `G` a group, `S` a `K`-algebra equipped with a `K`-algebra
homomorphism `φ : K[G] → S` (so that `S` is a `K[G]`-bimodule and a right `K[G]`-module),
and `X` a right `K[G]`-module which is a `K`-module compatibly.  This file sets up the
*diagonal* left `K[G]`-module structure on `S ⊗[K] X`:

`g • (s ⊗ x) = (g · s · g⁻¹) ⊗ (x · g⁻¹)`,  where `g` is identified with the element
`φ (single g 1)` of `S` and acts on `S` by conjugation.

This is the module appearing throughout Jaikin-Zapirain--Linton, §5 (there `S = D_{K[G]}`),
in Lemma 5.1 and Lemma 5.2.  We record the individual `K`-linear maps `diagLin g`
(`z ↦ g • z`), their group-action laws, and the formula for the action of a general
element of `K[G]` (`diagAct`), which is the content of the diagonal module.
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
variable (X : Type u) [AddCommGroup X] [Module K X]
variable [Module (MonoidAlgebra K G)ᵐᵒᵖ X]
variable [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ X]
variable [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ X]

/-- The group element `g ∈ G`, viewed as an element of `S` through `φ`. -/
noncomputable def gElem (g : G) : S := φ (MonoidAlgebra.single g (1 : K))

@[simp] theorem gElem_one : gElem K G S φ 1 = 1 := by
  rw [gElem, ← MonoidAlgebra.one_def, map_one]

theorem gElem_mul (g h : G) :
    gElem K G S φ (g * h) = gElem K G S φ g * gElem K G S φ h := by
  have hsingle : (MonoidAlgebra.single g (1 : K)) * (MonoidAlgebra.single h (1 : K)) =
      MonoidAlgebra.single (g * h) (1 : K) := by
    rw [MonoidAlgebra.single_mul_single, mul_one]
  rw [gElem, gElem, gElem, ← hsingle, map_mul]

theorem gElem_mul_gElem_inv (g : G) : gElem K G S φ g * gElem K G S φ g⁻¹ = 1 := by
  rw [← gElem_mul, mul_inv_cancel, gElem_one]

/-- Conjugation by `g` on `S`, as a `K`-linear map. -/
noncomputable def conjLin (g : G) : S →ₗ[K] S :=
  (LinearMap.mulRight K (gElem K G S φ g⁻¹)).comp (LinearMap.mulLeft K (gElem K G S φ g))

@[simp] theorem conjLin_apply (g : G) (s : S) :
    conjLin K G S φ g s = gElem K G S φ g * s * gElem K G S φ g⁻¹ := rfl

@[simp] theorem conjLin_one : conjLin K G S φ 1 = LinearMap.id := by
  ext s
  simp [conjLin_apply]

theorem conjLin_mul (g h : G) :
    conjLin K G S φ (g * h) = (conjLin K G S φ g).comp (conjLin K G S φ h) := by
  ext s
  simp only [conjLin_apply, LinearMap.comp_apply, gElem_mul, mul_inv_rev, mul_assoc]

/-- The action of `g` on `X`: the right action by `g⁻¹` (`x ↦ x · g⁻¹`). -/
noncomputable def actLin (g : G) : X →ₗ[K] X where
  toFun x := op (MonoidAlgebra.single g⁻¹ (1 : K)) • x
  map_add' x y := smul_add _ _ _
  map_smul' k x := (smul_comm k (op (MonoidAlgebra.single g⁻¹ (1 : K))) x).symm

@[simp] theorem actLin_apply (g : G) (x : X) :
    actLin K G X g x = op (MonoidAlgebra.single g⁻¹ (1 : K)) • x := rfl

@[simp] theorem actLin_one : actLin K G X 1 = LinearMap.id := by
  ext x
  rw [actLin_apply, inv_one, ← MonoidAlgebra.one_def]
  simp

theorem actLin_mul (g h : G) :
    actLin K G X (g * h) = (actLin K G X g).comp (actLin K G X h) := by
  have hsingle : (MonoidAlgebra.single h⁻¹ (1 : K)) * (MonoidAlgebra.single g⁻¹ (1 : K)) =
      MonoidAlgebra.single (g * h)⁻¹ (1 : K) := by
    rw [MonoidAlgebra.single_mul_single, mul_one, mul_inv_rev]
  ext x
  rw [actLin_apply, LinearMap.comp_apply, actLin_apply, actLin_apply, ← hsingle, op_mul, mul_smul]

/-- The `K`-linear map `z ↦ g • z` on `S ⊗[K] X`. -/
noncomputable def diagLin (g : G) : (S ⊗[K] X) →ₗ[K] (S ⊗[K] X) :=
  TensorProduct.map (conjLin K G S φ g) (actLin K G X g)

@[simp] theorem diagLin_tmul (g : G) (s : S) (x : X) :
    diagLin K G S φ X g (s ⊗ₜ[K] x) =
      (gElem K G S φ g * s * gElem K G S φ g⁻¹) ⊗ₜ[K]
        (op (MonoidAlgebra.single g⁻¹ (1 : K)) • x) := by
  simp [diagLin, conjLin, actLin]

@[simp] theorem diagLin_one : diagLin K G S φ X 1 = LinearMap.id := by
  rw [diagLin, conjLin_one, actLin_one, TensorProduct.map_id]

/-- The conjugation action is a group action. -/
theorem diagLin_mul (g h : G) :
    diagLin K G S φ X (g * h) = (diagLin K G S φ X g).comp (diagLin K G S φ X h) := by
  rw [diagLin, diagLin, diagLin, conjLin_mul, actLin_mul, TensorProduct.map_comp]


/-- The conjugation action, as a monoid homomorphism `G →* Module.End K (S ⊗[K] X)`. -/
noncomputable def diagMonoidHom : G →* Module.End K (S ⊗[K] X) where
  toFun g := diagLin K G S φ X g
  map_one' := diagLin_one K G S φ X
  map_mul' g h := by
    rw [diagLin_mul]
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.comp_apply, Module.End.mul_apply]

/-- The diagonal action of `K[G]` on `S ⊗[K] X`, as a `K`-algebra homomorphism into the
endomorphism ring. -/
noncomputable def diagRingHom : MonoidAlgebra K G →ₐ[K] Module.End K (S ⊗[K] X) :=
  (MonoidAlgebra.lift K (Module.End K (S ⊗[K] X)) G) (diagMonoidHom K G S φ X)

@[simp] theorem diagRingHom_single (g : G) (c : K) :
    diagRingHom K G S φ X (MonoidAlgebra.single g c) = c • diagLin K G S φ X g := by
  rw [diagRingHom, MonoidAlgebra.lift_single]
  rfl

/-- **The diagonal (conjugation) `K[G]`-module structure on `S ⊗[K] X`**:
`g • (s ⊗ x) = (g · s · g⁻¹) ⊗ (x · g⁻¹)`. -/
noncomputable def diagModule : Module (MonoidAlgebra K G) (S ⊗[K] X) where
  smul a z := diagRingHom K G S φ X a z
  one_smul z := by
    show diagRingHom K G S φ X 1 z = z
    rw [map_one, Module.End.one_apply]
  mul_smul a b z := by
    show diagRingHom K G S φ X (a * b) z = diagRingHom K G S φ X a (diagRingHom K G S φ X b z)
    rw [map_mul, Module.End.mul_apply]
  smul_zero a := map_zero _
  smul_add a x y := map_add _ x y
  add_smul a b z := by
    show diagRingHom K G S φ X (a + b) z =
      diagRingHom K G S φ X a z + diagRingHom K G S φ X b z
    rw [map_add]
    rfl
  zero_smul z := by
    show diagRingHom K G S φ X 0 z = 0
    rw [map_zero]
    rfl

/-- The computation rule for the diagonal action on pure tensors. -/
theorem diagModule_single_tmul (g : G) (c : K) (s : S) (x : X) :
    letI := diagModule K G S φ X
    (MonoidAlgebra.single g c) • (s ⊗ₜ[K] x) =
      c • ((gElem K G S φ g * s * gElem K G S φ g⁻¹) ⊗ₜ[K]
        (op (MonoidAlgebra.single g⁻¹ (1 : K)) • x)) := by
  letI := diagModule K G S φ X
  rw [show (MonoidAlgebra.single g c) • (s ⊗ₜ[K] x) =
      diagRingHom K G S φ X (MonoidAlgebra.single g c) (s ⊗ₜ[K] x) from rfl]
  rw [diagRingHom_single]
  simp only [LinearMap.smul_apply, diagLin_tmul]

/-- The diagonal action is compatible with the `K`-module structure. -/
theorem diagIsScalarTower :
    letI := diagModule K G S φ X
    IsScalarTower K (MonoidAlgebra K G) (S ⊗[K] X) := by
  letI := diagModule K G S φ X
  refine ⟨fun k a z => ?_⟩
  show diagRingHom K G S φ X (k • a) z = k • (diagRingHom K G S φ X a z)
  rw [map_smul, LinearMap.smul_apply]

end Work.ORFlatness
