import Mathlib
import Submission.Work.Tower.FrattiniLayer.Basic
import Submission.Work.Tower.FrattiniLayer.baseChange_unramified
import Submission.Work.Tower.FrattiniLayer.sup_left_injective

/-!
# Finiteness of the cubic unramified set transfers from a quadratic base to `F`

Let `F` be a number field, `Ω/F` any field extension, and `Z/F` a *quadratic* Galois extension of
`F` inside `Ω` (in the application `Z = F⟮ζ₃⟯`).  This file proves that if the set of cubic
everywhere unramified Galois extensions of `Z` inside `Ω` is finite, then the same is true over
`F`:

`finite_cubicUnramifiedSet_of_le`.

The mechanism is a base-change injection: a cubic everywhere unramified Galois extension `M/F`
with `Z` adjoined gives a cubic everywhere unramified Galois extension `M·Z / Z`
(`isCubicUnramified_overBase_sup`), and no two distinct `M`'s give the same one
(`overBase_sup_injective`, proved from `sup_left_injective`).  Degrees are coprime (`3` and `2`),
so `M` and `Z` are linearly disjoint, `[M·Z : F] = 6` and hence `[M·Z : Z] = 3`; Galoisness and
unramifiedness are inherited from `M/F` (the latter by `baseChange_unramified`).
-/

open NumberField

namespace Work.Tower.FrattiniLayer

/-- **Base change of a cubic everywhere unramified extension along a quadratic field.**

If `M/F` is a cubic everywhere unramified Galois extension of the number field `F` and
`Z/F ⊆ Ω/F` is a quadratic Galois extension of `F`, then the compositum `M·Z`, viewed as an
intermediate field of `Ω/Z` via `overBase`, is again a cubic everywhere unramified Galois
extension — this time of `Z`.

* the degree is `3`: `M` and `Z` are linearly disjoint over `F` because `3` and `2` are coprime,
  hence `[M·Z : Z] = [M : F] = 3`;
* the extension is Galois over `Z`: a compositum of Galois extensions of `F` is Galois over `F`,
  and restricts to a Galois extension over any intermediate field;
* unramifiedness is `baseChange_unramified`. -/
theorem isCubicUnramified_overBase_sup {F Ω : Type*} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (Z : IntermediateField F Ω) [IsGalois F Z] (hZ : Module.finrank F Z = 2)
    {M : IntermediateField F Ω} (hM : IsCubicUnramified F Ω M) :
    IsCubicUnramified ↥Z Ω (overBase Z (M ⊔ Z) le_sup_right) := by
  obtain ⟨hfin3, hgal, hunram⟩ := hM
  haveI : FiniteDimensional F ↥M := Module.finite_of_finrank_pos (by rw [hfin3]; norm_num)
  haveI : FiniteDimensional F ↥Z := Module.finite_of_finrank_pos (by rw [hZ]; norm_num)
  haveI : IsGalois F ↥M := hgal
  haveI : NumberField ↥M := NumberField.of_module_finite F ↥M
  haveI : NumberField ↥Z := NumberField.of_module_finite F ↥Z
  -- Unramifiedness over `Z` is base change of unramifiedness of `M/F`.
  have hUnram : IsUnramifiedOver ↥Z ↥(overBase Z (M ⊔ Z) le_sup_right) :=
    baseChange_unramified M Z hunram
  refine ⟨?_, ?_, hUnram⟩
  · -- The relative degree is `3`.
    have hdisj : M.LinearDisjoint Z :=
      IntermediateField.LinearDisjoint.of_finrank_coprime (by rw [hfin3, hZ]; decide)
    have h6 : Module.finrank F ↥(M ⊔ Z) = 6 := by
      have h := hdisj.finrank_sup
      rw [hfin3, hZ] at h
      omega
    letI algZL : Algebra ↥Z ↥(M ⊔ Z) :=
      (IntermediateField.inclusion (le_sup_right : Z ≤ M ⊔ Z)).toAlgebra
    haveI : IsScalarTower F ↥Z ↥(M ⊔ Z) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : FaithfulSMul ↥Z ↥(M ⊔ Z) :=
      (faithfulSMul_iff_algebraMap_injective ↥Z ↥(M ⊔ Z)).mpr (RingHom.injective _)
    have h3 : Module.finrank ↥Z ↥(M ⊔ Z) = 3 := by
      have h := Module.finrank_mul_finrank' (R := F) (S := ↥Z) (T := ↥(M ⊔ Z))
      rw [hZ, h6] at h
      omega
    exact (LinearEquiv.finrank_eq
      (AlgEquiv.refl : ↥(overBase Z (M ⊔ Z) le_sup_right) ≃ₐ[↥Z] ↥(M ⊔ Z)).toLinearEquiv).trans h3
  · -- Galoisness over `Z`.
    letI algZL : Algebra ↥Z ↥(M ⊔ Z) :=
      (IntermediateField.inclusion (le_sup_right : Z ≤ M ⊔ Z)).toAlgebra
    haveI : IsScalarTower F ↥Z ↥(M ⊔ Z) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    -- The compositum `M ⊔ Z` is Galois over `F`: it is the `iSup` of two normal, separable
    -- extensions.
    have hsup : (M ⊔ Z : IntermediateField F Ω) = ⨆ i : Bool, (if i then M else Z) := by
      rw [iSup_bool_eq]; simp
    haveI hN' : ∀ i : Bool, Normal F ↥(if i then M else Z) := by
      intro i; cases i <;> simp <;> infer_instance
    haveI hS' : ∀ i : Bool, Algebra.IsSeparable F ↥(if i then M else Z) := by
      intro i; cases i <;> simp <;> infer_instance
    haveI hNorm : Normal F ↥(M ⊔ Z) :=
      hsup ▸ IntermediateField.normal_iSup F Ω (fun i : Bool => if i then M else Z)
    haveI hSep : Algebra.IsSeparable F ↥(M ⊔ Z) :=
      hsup ▸ IntermediateField.isSeparable_iSup F Ω (t := fun i : Bool => if i then M else Z)
    haveI : IsGalois F ↥(M ⊔ Z) := inferInstance
    -- Galoisness descends to the intermediate field `Z`.
    haveI hgalZL : IsGalois ↥Z ↥(M ⊔ Z) := IsGalois.tower_top_of_isGalois F ↥Z ↥(M ⊔ Z)
    exact IsGalois.of_algEquiv (F := ↥Z) (E := ↥(M ⊔ Z))
      (E' := ↥(overBase Z (M ⊔ Z) le_sup_right))
      (AlgEquiv.refl : ↥(overBase Z (M ⊔ Z) le_sup_right) ≃ₐ[↥Z] ↥(M ⊔ Z))

/-- **The base-change map is injective on the cubic unramified set.**

Two cubic everywhere unramified Galois extensions `M₁, M₂` of `F` inside `Ω` that become equal
after adjoining the quadratic Galois extension `Z/F` are already equal: `M₁ = M₂`.  This is
`sup_left_injective`. -/
theorem overBase_sup_injective {F Ω : Type*} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (Z : IntermediateField F Ω) [IsGalois F Z] (hZ : Module.finrank F Z = 2)
    {M₁ M₂ : IntermediateField F Ω} (h₁ : IsCubicUnramified F Ω M₁)
    (h₂ : IsCubicUnramified F Ω M₂)
    (heq : overBase Z (M₁ ⊔ Z) le_sup_right = overBase Z (M₂ ⊔ Z) le_sup_right) :
    M₁ = M₂ := by
  have hcoe : ((overBase Z (M₁ ⊔ Z) le_sup_right : IntermediateField ↥Z Ω) : Set Ω) =
      ((overBase Z (M₂ ⊔ Z) le_sup_right : IntermediateField ↥Z Ω) : Set Ω) := by rw [heq]
  rw [coe_overBase, coe_overBase] at hcoe
  exact sup_left_injective Z hZ h₁ h₂ (SetLike.coe_set_eq.mp hcoe)

/-- **Finiteness of the cubic everywhere unramified set descends from a quadratic extension.**

Let `F` be a number field, `Ω/F` an extension, and `Z/F ⊆ Ω` a quadratic Galois extension of `F`
containing a primitive third root of unity.  If there are finitely many cubic everywhere
unramified Galois extensions of `Z` inside `Ω`, then there are finitely many such extensions
of `F` inside `Ω`. -/
theorem finite_cubicUnramifiedSet_of_le {F Ω : Type*} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (Z : IntermediateField F Ω) [IsGalois F Z] (hZ : Module.finrank F Z = 2)
    (hζ : (primitiveRoots 3 ↥Z).Nonempty)
    (hfin : (Work.Tower.FrattiniLayer.cubicUnramifiedSet ↥Z Ω).Finite) :
    (Work.Tower.FrattiniLayer.cubicUnramifiedSet F Ω).Finite := by
  refine Set.Finite.of_injOn
    (f := fun M : IntermediateField F Ω => overBase Z (M ⊔ Z) le_sup_right) ?_ ?_ hfin
  · -- Every cubic unramified `M/F` is sent into the cubic unramified set over `Z`.
    intro M hM
    exact isCubicUnramified_overBase_sup Z hZ hM
  · -- The map is injective on the cubic unramified set.
    intro M₁ h₁ M₂ h₂ heq
    exact overBase_sup_injective Z hZ h₁ h₂ heq

end Work.Tower.FrattiniLayer
