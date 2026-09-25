import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq

/-!
# `U`-orbits of places are the fibres of the restriction to `K'^U`

For an open subgroup `U ≤ Gal(K'/K)` (`K` a number field, `K'` a separable closure), the
`U`-orbits on the valuation subrings of `K'` are exactly the fibres of the restriction map
`A ↦ A.comap (algebraMap K'^U K')`: two places of `K'` lie in the same `U`-orbit if and only if
they induce the same place of `F := K'^U`.

The forward direction is elementary (`σ ∈ U` fixes `F` pointwise); the converse is the transitivity
of the Galois action on the places above a fixed place
(`Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq`, i.e. the finite case plus compactness) and
uses that `F/K` is finite — hence a number field — because `U` is open
(`InfiniteGalois.isOpen_iff_finite`).

This is the dictionary that lets the route-B lemmas refer to `¬ InOrbit U A₁ A₂`
(`Submission/Work/NUV2/LC/RouteB/Defs.lean`) as "`A₁` and `A₂` lie over different places of `F`".
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Pointwise

namespace NK.NUV2.LC.RouteB

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **Places in one `U`-orbit have the same restriction to `K'^U`.** -/
theorem comap_eq_of_inOrbit (U : Subgroup Gal(K'/K))
    {A B : ValuationSubring K'} (h : InOrbit (K := K) (K' := K') U A B) :
    A.comap (algebraMap ↥(IntermediateField.fixedField U) K') =
      B.comap (algebraMap ↥(IntermediateField.fixedField U) K') := by
  obtain ⟨σ, hσU, hσ⟩ := h
  subst hσ
  have key : ∀ y : ↥(IntermediateField.fixedField U),
      σ⁻¹ (algebraMap ↥(IntermediateField.fixedField U) K' y) =
        algebraMap ↥(IntermediateField.fixedField U) K' y := by
    intro y
    exact (IntermediateField.mem_fixedField_iff U (y : K')).mp y.2 σ⁻¹ (inv_mem hσU)
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hconv : (σ⁻¹ : Gal(K'/K)) • (algebraMap ↥(IntermediateField.fixedField U) K' x) =
      algebraMap ↥(IntermediateField.fixedField U) K' x := by simpa using key x
  rw [hconv]

/-- **Places with the same restriction to `K'^U` are `U`-conjugate** (for `U` open, so that
`K'^U` is a number field). -/
theorem inOrbit_of_comap_eq (U : Subgroup Gal(K'/K)) (hUopen : IsOpen (U : Set Gal(K'/K)))
    {A B : ValuationSubring K'} (hA : A.comap (algebraMap K K') ≠ ⊤)
    (h : A.comap (algebraMap ↥(IntermediateField.fixedField U) K') =
      B.comap (algebraMap ↥(IntermediateField.fixedField U) K')) :
    InOrbit (K := K) (K' := K') U A B := by
  haveI : IsGalois K K' := inferInstance
  have hUcl : IsClosed (U : Set Gal(K'/K)) := Subgroup.isClosed_of_isOpen U hUopen
  have hFix : (IntermediateField.fixedField U).fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, hUcl⟩
  have hFin : FiniteDimensional K ↥(IntermediateField.fixedField U) := by
    rw [← InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField U), hFix]
    exact hUopen
  haveI : FiniteDimensional K ↥(IntermediateField.fixedField U) := hFin
  haveI : NumberField ↥(IntermediateField.fixedField U) :=
    NumberField.of_module_finite K ↥(IntermediateField.fixedField U)
  have hA' : A.comap (algebraMap ↥(IntermediateField.fixedField U) K') ≠ ⊤ := by
    intro htop
    apply hA
    have h1 : (A.comap (algebraMap ↥(IntermediateField.fixedField U) K')).comap
        (algebraMap K ↥(IntermediateField.fixedField U)) = A.comap (algebraMap K K') := by
      rw [ValuationSubring.comap_comap,
        IsScalarTower.algebraMap_eq K ↥(IntermediateField.fixedField U) K']
    rw [← h1, htop]
    ext x
    simp [ValuationSubring.mem_comap]
  obtain ⟨σ, hσ⟩ := Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq
    (F := ↥(IntermediateField.fixedField U)) (K' := K') A B hA' h
  refine ⟨AlgEquiv.restrictScalars K σ, ?_, ?_⟩
  · have hmem : AlgEquiv.restrictScalars K σ ∈
        (IntermediateField.fixedField U).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hx' : σ (algebraMap ↥(IntermediateField.fixedField U) K'
          (⟨x, hx⟩ : ↥(IntermediateField.fixedField U))) =
          algebraMap ↥(IntermediateField.fixedField U) K'
            (⟨x, hx⟩ : ↥(IntermediateField.fixedField U)) :=
        AlgEquiv.commutes σ (⟨x, hx⟩ : ↥(IntermediateField.fixedField U))
      simpa using hx'
    rwa [hFix] at hmem
  · rw [← hσ]
    ext x
    simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simp

/-- **The orbits of an open `U` are the fibres of the restriction to `K'^U`.** -/
theorem inOrbit_iff_comap_eq (U : Subgroup Gal(K'/K)) (hUopen : IsOpen (U : Set Gal(K'/K)))
    {A B : ValuationSubring K'} (hA : A.comap (algebraMap K K') ≠ ⊤) :
    InOrbit (K := K) (K' := K') U A B ↔
      A.comap (algebraMap ↥(IntermediateField.fixedField U) K') =
        B.comap (algebraMap ↥(IntermediateField.fixedField U) K') :=
  ⟨comap_eq_of_inOrbit U, fun h => inOrbit_of_comap_eq U hUopen hA h⟩

end NK.NUV2.LC.RouteB
