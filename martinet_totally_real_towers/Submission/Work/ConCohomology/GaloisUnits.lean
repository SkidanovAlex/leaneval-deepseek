/-
Copyright: the martinet_totally_real_towers team.

# The Galois module `Lˣ`

For a field extension `L/K`, the Galois group `Gal(L/K) = L ≃ₐ[K] L` acts on the multiplicative
group `Lˣ`; as coefficient modules are written additively in this chapter, we record the resulting
`DistribMulAction (L ≃ₐ[K] L) (Additive Lˣ)` and, in the Galois case with the Krull topology, the
fact that this is a *discrete* module (the stabilizer of every unit is open).
-/

import Submission.Work.ConCohomology.Functoriality

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

section Units

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The action of `S ≃ₐ[R] S` on `Additive Sˣ`, i.e. on `Sˣ` written additively. -/
def additiveUnitsSmul (g : S ≃ₐ[R] S) (x : Additive Sˣ) : Additive Sˣ :=
  Additive.ofMul (g • x.toMul)

@[simp] lemma additiveUnitsSmul_apply (g : S ≃ₐ[R] S) (x : Additive Sˣ) :
    additiveUnitsSmul g x = Additive.ofMul (g • x.toMul) := rfl

lemma additiveUnitsSmul_toMul (g : S ≃ₐ[R] S) (x : Additive Sˣ) :
    (additiveUnitsSmul g x).toMul = g • x.toMul := rfl

/-- The natural action of `S ≃ₐ[R] S` on `Additive Sˣ` (the additive notation for `Sˣ`). -/
instance instDistribMulActionAdditiveUnits : DistribMulAction (S ≃ₐ[R] S) (Additive Sˣ) where
  smul := additiveUnitsSmul
  one_smul x := by
    show additiveUnitsSmul 1 x = x
    simp [additiveUnitsSmul]
  mul_smul g h x := by
    show additiveUnitsSmul (g * h) x = additiveUnitsSmul g (additiveUnitsSmul h x)
    simp [additiveUnitsSmul, mul_smul]
  smul_zero g := by
    show additiveUnitsSmul g 0 = 0
    simp [additiveUnitsSmul]
  smul_add g x y := by
    show additiveUnitsSmul g (x + y) = additiveUnitsSmul g x + additiveUnitsSmul g y
    simp only [additiveUnitsSmul_apply, toMul_add, smul_mul', ofMul_mul]

/-- The action on `Additive Sˣ` is the action on `Sˣ`. -/
lemma toMul_smul_additiveUnits (g : S ≃ₐ[R] S) (x : Additive Sˣ) :
    (g • x).toMul = g • x.toMul := rfl

lemma smul_additiveUnits_eq (g : S ≃ₐ[R] S) (x : Sˣ) :
    (g • Additive.ofMul x).toMul = g • x := rfl

end Units

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- The stabilizer of a unit of `L` under the Galois action is open in the Krull topology. -/
lemma isLocallyConstant_smul_units (x : Additive Lˣ) :
    IsLocallyConstant fun σ : Gal(L/K) => σ • x := by
  rw [IsLocallyConstant.iff_exists_open]
  intro σ₀
  have hx : IsIntegral K (x.toMul : L) := by
    haveI : Algebra.IsAlgebraic K L := IsGalois.to_normal.toIsAlgebraic
    exact (Algebra.IsAlgebraic.isAlgebraic (x.toMul : L)).isIntegral
  haveI : FiniteDimensional K ↥(IntermediateField.adjoin K {(x.toMul : L)}) :=
    IntermediateField.adjoin.finiteDimensional hx
  set E : IntermediateField K L := IntermediateField.adjoin K {(x.toMul : L)} with hE
  have hU : IsOpen (E.fixingSubgroup : Set Gal(L/K)) := E.fixingSubgroup_isOpen
  have hcont : Continuous fun y : Gal(L/K) => σ₀⁻¹ * y := continuous_const.mul continuous_id
  refine ⟨{y : Gal(L/K) | σ₀⁻¹ * y ∈ (E.fixingSubgroup : Set Gal(L/K))},
    hU.preimage hcont, by simp, ?_⟩
  intro y hy
  have hmem : (σ₀⁻¹ * y) ∈ E.fixingSubgroup := hy
  have hL : (σ₀⁻¹ * y) • (x.toMul : L) = (x.toMul : L) :=
    (IntermediateField.mem_fixingSubgroup_iff E (σ₀⁻¹ * y)).mp hmem _ (by
      rw [hE]
      exact IntermediateField.subset_adjoin K ({((x.toMul : Lˣ) : L)} : Set L) (Set.mem_singleton _))
  have hunit : (σ₀⁻¹ * y) • x.toMul = x.toMul := by
    apply Units.ext
    simpa using hL
  have hux : (σ₀⁻¹ * y) • x = x := by
    apply Additive.toMul.injective
    rw [toMul_smul_additiveUnits, hunit]
  calc y • x = (σ₀ * (σ₀⁻¹ * y)) • x := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    _ = σ₀ • ((σ₀⁻¹ * y) • x) := mul_smul _ _ _
    _ = σ₀ • x := by rw [hux]

/-- `Additive Lˣ` is a discrete `Gal(L/K)`-module for a Galois extension `L/K`. -/
instance instIsDiscreteGModuleUnits : IsDiscreteGModule Gal(L/K) (Additive Lˣ) where
  isLocallyConstant_smul := isLocallyConstant_smul_units

end Galois

end Work.ConCohomology
