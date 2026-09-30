import Mathlib
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMapTensor
import Submission.Work.CurveBasics.Curve.BCSquare.SectionsTensor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

set_option linter.style.haveILetI false

universe u

/-- **Injectivity of `tensorLift`.**

For a curve `C` over a field `k`, a field extension `F/k` and a base-change square
`S : BCSquare C C'`, the natural map

`tensorLift S : F ⊗[k] K(C) ⟶ K(C')`,  `c ⊗ x ↦ c · S.fieldMap x`

is injective.  This is the linear disjointness of `F` and the function field `K(C)` inside the
function field of the base change: both are subfields of `K(C')` and `K(C) ⊗[k] F` is the
localisation of the coordinate ring `Γ(C,W) ⊗[k] F` of an affine chart of the base change at
the non-zero divisors of `Γ(C,W)`, which embeds into `K(C')` because the base change is
integral.

The proof is by reduction to an affine chart `W ⊆ C`: for the affine open `W` and
`A = Γ(C,W)`, the base change `S.π ⁻¹ᵁ W` has coordinate ring `A ⊗[k] F` (`sectionsLift`, an
isomorphism), which maps injectively into `K(C')`.  Since `K(C) ⊗[k] F` is the localisation of
`A ⊗[k] F` at the non-zero divisors of `A`, an element of the kernel of `tensorLift` can be
cleared of denominators, and then must already vanish in `A ⊗[k] F`. -/
theorem tensorLift_injective {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') :
    Function.Injective (Curve.BCSquare.tensorLift S) := by
  classical
  -- a nonempty affine open chart `W ⊆ C`
  obtain ⟨x⟩ : Nonempty C.left := inferInstance
  obtain ⟨_, ⟨W, hWaff, rfl⟩, hxW, -⟩ :=
    C.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hW : AlgebraicGeometry.IsAffineOpen W := hWaff
  haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
  haveI : Nonempty (S.π ⁻¹ᵁ W) := inferInstance
  -- `A = Γ(C,W)` is a domain with fraction field `K(C)`
  haveI hFrac : IsFractionRing Γ(C.left, W) C.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen C.left W hW
  haveI hTower : IsScalarTower k Γ(C.left, W) C.functionField :=
    isScalarTower_sections C W
  -- the `A ⊗[k] F`-algebra structure on `K(C) ⊗[k] F` exhibiting it as a localisation
  letI : Algebra (Γ(C.left, W) ⊗[k] F) (C.functionField ⊗[k] F) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k Γ(C.left, W) C.functionField)
      (AlgHom.id k F)).toRingHom.toAlgebra
  haveI hST : IsScalarTower Γ(C.left, W) (Γ(C.left, W) ⊗[k] F) (C.functionField ⊗[k] F) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    show (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k Γ(C.left, W) C.functionField)
      (AlgHom.id k F)) (a ⊗ₜ[k] (1 : F))
      = algebraMap Γ(C.left, W) C.functionField a ⊗ₜ[k] (1 : F)
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have hH : (algebraMap (Γ(C.left, W) ⊗[k] F) (C.functionField ⊗[k] F)).comp
      (Algebra.TensorProduct.includeRight (R := k) (A := Γ(C.left, W)) (B := F)).toRingHom
      = (Algebra.TensorProduct.includeRight (R := k) (A := C.functionField) (B := F)).toRingHom := by
    ext s
    show (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k Γ(C.left, W) C.functionField)
      (AlgHom.id k F)) (1 ⊗ₜ[k] s) = 1 ⊗ₜ[k] s
    simp
  haveI hloc : IsLocalization
      (Algebra.algebraMapSubmonoid (Γ(C.left, W) ⊗[k] F) (nonZeroDivisors Γ(C.left, W)))
      (C.functionField ⊗[k] F) :=
    IsLocalization.tensorProduct_tensorProduct (R := k) (S := F) (A := Γ(C.left, W))
      (M := nonZeroDivisors Γ(C.left, W)) (B := C.functionField) hH
  -- the maps on the affine chart
  let ψ : (C.functionField ⊗[k] F) →+* C'.functionField :=
    (tensorLift S).comp (Algebra.TensorProduct.comm k C.functionField F).toRingHom
  let φ : (Γ(C.left, W) ⊗[k] F) →+* C'.functionField :=
    ψ.comp (algebraMap (Γ(C.left, W) ⊗[k] F) (C.functionField ⊗[k] F))
  -- the value of the localisation map on pure tensors
  have hloc_tmul (a : Γ(C.left, W)) (c : F) :
      algebraMap (Γ(C.left, W) ⊗[k] F) (C.functionField ⊗[k] F) (a ⊗ₜ[k] c)
        = algebraMap Γ(C.left, W) C.functionField a ⊗ₜ[k] c := by
    trans (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k Γ(C.left, W) C.functionField)
      (AlgHom.id k F)) (a ⊗ₜ[k] c)
    · rfl
    · rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
  -- the value of `ψ` on arbitrary elements
  have hψ_apply (y : C.functionField ⊗[k] F) :
      ψ y = tensorLift S ((Algebra.TensorProduct.comm k C.functionField F) y) := by
    show (tensorLift S) ((Algebra.TensorProduct.comm k C.functionField F).toRingHom y) = _
    rfl
  -- `φ` factors through the sections of the affine chart
  have hφeq : φ = (C'.germToFunctionField (S.π ⁻¹ᵁ W)).hom.comp (sectionsLift S W hW) := by
    refine ringHom_ext_tensor ?_ ?_
    · intro a
      show ψ (algebraMap (Γ(C.left, W) ⊗[k] F) (C.functionField ⊗[k] F)
          (a ⊗ₜ[k] (1 : F)))
        = (C'.germToFunctionField (S.π ⁻¹ᵁ W)).hom (sectionsLift S W hW (a ⊗ₜ[k] (1 : F)))
      rw [hloc_tmul a 1, sectionsLift_tmul_one S W hW a, hψ_apply,
        Algebra.TensorProduct.comm_tmul, tensorLift_one_tmul]
      simpa only [RingHom.algebraMap_toAlgebra] using fieldMap_germToFunctionField S W a
    · intro c
      show ψ (algebraMap (Γ(C.left, W) ⊗[k] F) (C.functionField ⊗[k] F)
          ((1 : Γ(C.left, W)) ⊗ₜ[k] c))
        = (C'.germToFunctionField (S.π ⁻¹ᵁ W)).hom
            (sectionsLift S W hW ((1 : Γ(C.left, W)) ⊗ₜ[k] c))
      rw [hloc_tmul 1 c, sectionsLift_one_tmul S W hW c, hψ_apply,
        Algebra.TensorProduct.comm_tmul]
      simp only [tensorLift_tmul, map_one, mul_one]
      show algebraMap F C'.functionField c
        = (C'.germToFunctionField (S.π ⁻¹ᵁ W)).hom
            (algebraMap F Γ(C'.left, S.π ⁻¹ᵁ W) c)
      exact (sections_algebraMap_eq C' (S.π ⁻¹ᵁ W) c).symm
  have hφinj : Function.Injective φ := by
    rw [hφeq]
    exact (Scheme.germToFunctionField_injective C'.left (S.π ⁻¹ᵁ W)).comp
      (sectionsLift_injective S W hW)
  -- an element of the kernel of `tensorLift` can be cleared of denominators
  have hker : ∀ z : F ⊗[k] C.functionField, tensorLift S z = 0 → z = 0 := by
    intro z hz
    set u : C.functionField ⊗[k] F := (Algebra.TensorProduct.comm k C.functionField F).symm z
      with hu
    have hzu : ψ u = 0 := by
      rw [hu, hψ_apply, AlgEquiv.apply_symm_apply, hz]
    obtain ⟨⟨w, s⟩, hs⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid (Γ(C.left, W) ⊗[k] F) (nonZeroDivisors Γ(C.left, W))) u
    have hw0 : w = 0 := by
      apply hφinj
      show ψ (algebraMap (Γ(C.left, W) ⊗[k] F) (C.functionField ⊗[k] F) w) = 0
      rw [← hs, map_mul, hzu, zero_mul]
    have hu0 : u = 0 :=
      IsUnit.mul_right_cancel (IsLocalization.map_units (C.functionField ⊗[k] F) s)
        (by rw [hs, hw0, map_zero, zero_mul])
    have hz_u : z = (Algebra.TensorProduct.comm k C.functionField F) u := by
      rw [hu, AlgEquiv.apply_symm_apply]
    rw [hz_u, hu0, map_zero]
  intro z w hzw
  have h0 : tensorLift S (z - w) = 0 := by rw [map_sub, hzw, sub_self]
  exact sub_eq_zero.mp (hker (z - w) h0)

end Work.CurveBasics.Curve.BCSquare
