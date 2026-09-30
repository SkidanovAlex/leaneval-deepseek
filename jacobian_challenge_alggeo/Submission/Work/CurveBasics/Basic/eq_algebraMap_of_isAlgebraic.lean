import Mathlib
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.Place.Coheight
import Submission.Work.CurveBasics.Basic.Sections
import Submission.Work.CurveBasics.Basic.isDomain_tensor_of_isOpenImmersion
import Submission.Work.CurveBasics.Basic.isDomain_tensor_fractionRing
import Submission.Work.CurveBasics.Basic.isDomain_tensor_sections

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open scoped Classical

namespace Work.CurveBasics.Basic

open Work.CurveBasics in
theorem eq_algebraMap_of_isAlgebraic {k : Type*} [Field k] (C : Curve k) {x : C.functionField}
    (hx : IsAlgebraic k x) : ∃ c : k, x = algebraMap k C.functionField c := by
  -- pick a non-empty affine open of `C`
  obtain ⟨x₀⟩ := (inferInstance : Nonempty C.left)
  let j := C.left.affineCover.idx x₀
  obtain ⟨i, hi⟩ := C.left.affineCover.covers x₀
  let U : C.left.Opens := (C.left.affineCover.f j).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (C.left.affineCover.f j)
  haveI : Nonempty U := ⟨⟨x₀, i, hi⟩⟩
  -- `L := k(x)`
  let L : IntermediateField k C.functionField := IntermediateField.adjoin k {x}
  haveI hfin : FiniteDimensional k L :=
    IntermediateField.adjoin.finiteDimensional (isAlgebraic_iff_isIntegral.mp hx)
  have hmem : x ∈ L := IntermediateField.mem_adjoin_simple_self k x
  -- `Γ(C, U) ⊗[k] L` and `K(C) ⊗[k] L` are domains
  have hD : IsDomain (Γ(C.left, U) ⊗[k] L) := Curve.isDomain_tensor_sections C hU L
  haveI : IsFractionRing Γ(C.left, U) ↥(C.functionField) :=
    functionField_isFractionRing_of_isAffineOpen C.left U hU
  haveI : IsScalarTower k Γ(C.left, U) ↥(C.functionField) := Curve.isScalarTower_sections C U
  have hD2 : IsDomain (↥(C.functionField) ⊗[k] L) :=
    isDomain_tensor_of_fractionRing (k := k) (A := Γ(C.left, U)) (L := L)
      (K := ↥(C.functionField)) hD
  haveI : IsDomain (↥(C.functionField) ⊗[k] L) := hD2
  -- hence `K(C) ⊗[k] L` is a field
  haveI hField : IsField (↥(C.functionField) ⊗[k] L) :=
    IsField.of_isDomain_of_finite ↥(C.functionField) (↥(C.functionField) ⊗[k] L)
  -- the multiplication map `K(C) ⊗[k] L ⟶ K(C)`
  let μ : ↥(C.functionField) ⊗[k] L →ₐ[k] ↥(C.functionField) :=
    (Algebra.TensorProduct.lmul' k).comp
      (Algebra.TensorProduct.map (AlgHom.id k ↥(C.functionField)) (IntermediateField.val L))
  have hsmul : ∀ (y : ↥(C.functionField)) (z : ↥(C.functionField) ⊗[k] L), μ (y • z) = y • μ z := by
    intro y z
    refine TensorProduct.inductionOn z ?_ ?_
    · intro x l
      simp only [μ, AlgHom.coe_comp, Function.comp_apply, TensorProduct.smul_tmul',
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.lmul'_apply_tmul,
        Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
      rw [mul_assoc]
    · intro a b ha hb
      simp only [smul_add, map_add, ha, hb]
  have hinj : Function.Injective μ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hz0
    obtain ⟨b, hb⟩ := hField.mul_inv_cancel hz0
    have h1 : (1 : ↥(C.functionField)) = 0 := by
      have hμ1 : μ (1 : ↥(C.functionField) ⊗[k] L) = 1 := by simp [μ, Algebra.TensorProduct.one_def]
      have h2 : μ (z * b) = μ (1 : ↥(C.functionField) ⊗[k] L) := by rw [hb]
      rw [map_mul, hz, zero_mul, hμ1] at h2
      exact h2.symm
    exact one_ne_zero h1
  let μₗ : (↥(C.functionField) ⊗[k] L) →ₗ[↥(C.functionField)] ↥(C.functionField) :=
    { toFun := μ, map_add' := μ.map_add, map_smul' := hsmul }
  -- dimension count
  have hle : Module.finrank ↥(C.functionField) (↥(C.functionField) ⊗[k] L) ≤ 1 := by
    calc Module.finrank ↥(C.functionField) (↥(C.functionField) ⊗[k] L)
        ≤ Module.finrank ↥(C.functionField) ↥(C.functionField) :=
          LinearMap.finrank_le_finrank_of_injective (f := μₗ) hinj
      _ = 1 := Module.finrank_self _
  have hkl : Module.finrank k L =
      Module.finrank ↥(C.functionField) (↥(C.functionField) ⊗[k] L) := by
    rw [Module.finrank_tensorProduct (R := ↥(C.functionField)) (S := k)
      (M := ↥(C.functionField)) (M' := L), Module.finrank_self, one_mul]
  have h1 : Module.finrank k L = 1 := by
    rw [hkl]
    exact le_antisymm hle Module.finrank_pos
  obtain ⟨c, hc⟩ :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := k) (E := ↥L)).mp h1 |>.2 ⟨x, hmem⟩
  refine ⟨c, ?_⟩
  have h2 := congrArg (fun y : L => (y : ↥(C.functionField))) hc
  simpa using h2.symm

end Work.CurveBasics.Basic
