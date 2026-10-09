import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.RamifiedPlacesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level inertia subgroups of the decomposition group of a place

For a number field `k`, an algebraic closure `Ω`, a finite place `B` of `Ω` and a finite normal
intermediate field `M` of `Ω/k`, this file defines the subgroup

  `Work.SSGRoute.levelSub B M ≤ Ω ≃ₐ[k] Ω`

of elements of the decomposition group `D_B` of `B` acting trivially, modulo the maximal ideal, on
the level subring `B ∩ M` (`B.comap (algebraMap ↥M Ω)`).  The main result is that the intersection
of all the `levelSub B M` over the finite normal `M` is exactly the set of inertia elements at `B`
(`Work.SSGRoute.mem_levelSub_iff`), a purely *level-theoretic* description of the global inertia
subgroup that does not use any local field/completion theory.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute
open scoped Pointwise
open _root_.SSGRoute

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- An element of the decomposition group preserves the condition `B.valuation _ < 1`. -/
lemma val_lt_one_smul_iff (B : ValuationSubring Ω) (δ : ↥(decomp k B)) (y : Ω) :
    B.valuation ((δ : Ω ≃ₐ[k] Ω) y) < 1 ↔ B.valuation y < 1 := by
  have hδ : (δ : Ω ≃ₐ[k] Ω) • B = B := MulAction.mem_stabilizer_iff.mp δ.2
  have hBinv : (δ : Ω ≃ₐ[k] Ω)⁻¹ • B = B := by
    exact MulAction.mem_stabilizer_iff.mp ((decomp k B).inv_mem δ.2)
  have hsub : (B.valuation.comap ((δ : Ω ≃ₐ[k] Ω) : Ω →+* Ω)).valuationSubring =
      B.valuation.valuationSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    ext z
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      ValuationSubring.valuation_le_one_iff]
    constructor
    · intro hz
      have h2 : (δ : Ω ≃ₐ[k] Ω)⁻¹ ((δ : Ω ≃ₐ[k] Ω) z) ∈ (δ : Ω ≃ₐ[k] Ω)⁻¹ • B :=
        Set.smul_mem_smul_set hz
      rw [hBinv] at h2
      simpa using h2
    · intro hz
      have h2 : (δ : Ω ≃ₐ[k] Ω) z ∈ (δ : Ω ≃ₐ[k] Ω) • B := Set.smul_mem_smul_set hz
      rwa [hδ] at h2
  have heq : (B.valuation.comap ((δ : Ω ≃ₐ[k] Ω) : Ω →+* Ω)).IsEquiv B.valuation :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub
  have h := Valuation.IsEquiv.lt_one_iff_lt_one heq (x := y)
  rwa [Valuation.comap_apply] at h

variable (B : ValuationSubring Ω)

/-- **The level subgroup at a finite normal intermediate field `M`**: the elements of the
decomposition group `D_B` acting trivially on `B ∩ M` modulo the maximal ideal. -/
noncomputable def levelSub (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] :
    Subgroup (Ω ≃ₐ[k] Ω) where
  carrier := {δ | δ ∈ decomp k B ∧ ∀ x : ↥(B.comap (algebraMap ↥M Ω)),
      B.valuation (δ ((x : ↥M) : Ω) - ((x : ↥M) : Ω)) < 1}
  mul_mem' := by
    rintro δ₁ δ₂ ⟨h1D, h1⟩ ⟨h2D, h2⟩
    refine ⟨mul_mem h1D h2D, fun x => ?_⟩
    have k1 : B.valuation ((δ₁ : Ω ≃ₐ[k] Ω)
        ((δ₂ : Ω ≃ₐ[k] Ω) ((x : ↥M) : Ω) - ((x : ↥M) : Ω))) < 1 := by
      rw [val_lt_one_smul_iff B ⟨δ₁, h1D⟩]; exact h2 x
    have k2 : B.valuation ((δ₁ : Ω ≃ₐ[k] Ω) ((x : ↥M) : Ω) - ((x : ↥M) : Ω)) < 1 := h1 x
    have key : (δ₁ * δ₂ : Ω ≃ₐ[k] Ω) ((x : ↥M) : Ω) - ((x : ↥M) : Ω)
        = ((δ₁ : Ω ≃ₐ[k] Ω) ((δ₂ : Ω ≃ₐ[k] Ω) ((x : ↥M) : Ω) - ((x : ↥M) : Ω)))
          + ((δ₁ : Ω ≃ₐ[k] Ω) ((x : ↥M) : Ω) - ((x : ↥M) : Ω)) := by
      simp only [AlgEquiv.mul_apply, map_sub]
      abel
    rw [key]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt k1 k2)
  one_mem' := by
    refine ⟨one_mem _, fun x => ?_⟩
    simp
  inv_mem' := by
    rintro δ ⟨h1D, h1⟩
    refine ⟨inv_mem h1D, fun x => ?_⟩
    rw [← val_lt_one_smul_iff B ⟨δ, h1D⟩]
    have h1' : (δ : Ω ≃ₐ[k] Ω) (((δ : Ω ≃ₐ[k] Ω)⁻¹) ((x : ↥M) : Ω)) = ((x : ↥M) : Ω) := by
      simp
    have key : (δ : Ω ≃ₐ[k] Ω) (((δ : Ω ≃ₐ[k] Ω)⁻¹) ((x : ↥M) : Ω) - ((x : ↥M) : Ω))
        = -((δ : Ω ≃ₐ[k] Ω) ((x : ↥M) : Ω) - ((x : ↥M) : Ω)) := by
      rw [map_sub, h1']
      ring
    rw [key, Valuation.map_neg]
    exact h1 x

lemma levelSub_le_decomp (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] :
    levelSub B M ≤ decomp k B := fun _ h => h.1

/-- The level subgroups shrink with the level. -/
lemma levelSub_antitone {M M' : IntermediateField k Ω} [FiniteDimensional k M] [Normal k M]
    [FiniteDimensional k M'] [Normal k M'] (h : M ≤ M') : levelSub B M' ≤ levelSub B M := by
  intro δ hδ
  refine ⟨hδ.1, fun x => ?_⟩
  have hx : ((x : ↥M) : Ω) ∈ M' := h (x : ↥M).2
  have hxB : algebraMap ↥M' Ω (⟨((x : ↥M) : Ω), hx⟩ : ↥M') ∈ B := by
    rw [IntermediateField.algebraMap_apply]; exact (ValuationSubring.mem_comap).mp x.2
  have hmem := hδ.2 (⟨⟨((x : ↥M) : Ω), hx⟩, hxB⟩ : ↥(B.comap (algebraMap ↥M' Ω)))
  simpa [IntermediateField.algebraMap_apply] using hmem

/-- **The intersection of the level subgroups is the inertia subgroup.** -/
theorem mem_levelSub_iff (δ : Ω ≃ₐ[k] Ω) :
    (∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M], δ ∈ levelSub B M) ↔
      SSGRoute.IsInertia k B δ := by
  constructor
  · intro h
    have hD : δ ∈ decomp k B := (h ⊥ : δ ∈ levelSub B ⊥).1
    refine ⟨hD, fun x hx => ?_⟩
    have halg : IsAlgebraic k x := Algebra.IsAlgebraic.isAlgebraic x
    let L₀ : IntermediateField k Ω := IntermediateField.adjoin k ({x} : Set Ω)
    haveI hL₀ : FiniteDimensional k L₀ := IntermediateField.adjoin.finiteDimensional halg.isIntegral
    let M : IntermediateField k Ω := IntermediateField.normalClosure k L₀ Ω
    haveI hMfd : FiniteDimensional k M := inferInstance
    haveI hMnorm : Normal k M := inferInstance
    have hxM : x ∈ M := IntermediateField.le_normalClosure L₀
      (IntermediateField.subset_adjoin k _ (Set.mem_singleton x))
    have hxB : algebraMap ↥M Ω (⟨x, hxM⟩ : ↥M) ∈ B := by
      rw [IntermediateField.algebraMap_apply]; exact hx
    have hmem := (h M : δ ∈ levelSub B M).2
      (⟨⟨x, hxM⟩, hxB⟩ : ↥(B.comap (algebraMap ↥M Ω)))
    simpa [IntermediateField.algebraMap_apply] using hmem
  · rintro ⟨hD, hval⟩ M _ _
    refine ⟨hD, fun x => ?_⟩
    exact hval _ ((ValuationSubring.mem_comap).mp x.2)

end Work.SSGRoute
