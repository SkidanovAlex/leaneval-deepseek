import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.Work.SSGRoute.ZConstruction.ZDataGlue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sixth conjunct from a class killing `G_Λ` (a route that needs no condition (b))

The node `Work.SSGRoute.shafarevich_z_construction` asks for a cochain `z` whose transfer
`X δ = ∑_{s : Gal(K/k)} s • z ((sec s)⁻¹ δ sec s)` vanishes on the decomposition group of every
finite place `B ∉ cs(S)` that is split in `Λ` (on an open subgroup of it, at least).

`ZConstruction/Reduction.lean` proves that this `∃ V` clause is *equivalent* to the cyclicity of
the transfer image (`Work.SSGRoute.exists_V_of_cyclic_transfer`,
`Work.SSGRoute.isCyclic_transfer_of_exists_V`), and `ZConstruction/ZDataBridge.lean` derives it from
Schmidt–Wingberg's sharpened condition (b) — which is what the arithmetic of §4 supplies.

This file records a **second, purely formal** sufficient condition: if `z` vanishes on the whole
subgroup `G_Λ = Λ.fixingSubgroup` (which is open, `Λ` being finite over `k`), then the sixth
conjunct holds at **every** place `B` split in `Λ`, with the explicit witness
`V = Λ.fixingSubgroup`.  Indeed `G_Λ` is normal in `G_k` (`Λ/k` is Galois), so

* the conjugates `(sec s)⁻¹ δ sec s` of `δ ∈ D_B ⊓ G_Λ` again lie in `G_Λ`, where `z` vanishes, so
  every term of the transfer is `0` — no condition (b), no cyclicity, no local Tate pairing;
* the two structural conditions of the `∃ V` clause hold for `V = G_Λ` because `Λ` is finite over
  `k`, hence `G_Λ ≤ G_k` has finite index (`D_B ⊓ G_Λ` is normalised by `D_B` by normality of `G_Λ`
  in `G_k`, and it is `D_B` itself when `D_B ≤ G_Λ`).

**Consequence.**  The node follows from the five elementary clauses of its conclusion plus
`∀ σ ∈ Λ.fixingSubgroup, z σ = 0` — a régime that mentions no transfer and no local arithmetic.
`Work.SSGRoute.ZConstruction.fixingSubgroup_normal_of_isGalois` is the (Mathlib-exported)
normality, recorded here in the workspace's vocabulary.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

section KillLambda

variable {Λ : IntermediateField k Ω} [FiniteDimensional k Λ] [IsGalois k Λ]

/-- **`G_Λ` is normal in `G_k`**: it is the kernel of the restriction `res k Λ` (which exists
because `Λ/k` is Galois).  This is the Mathlib instance
`IsGalois.fixingSubgroup_normal_of_isGalois` in the vocabulary of this development; the proof here
uses only `Λ/k` Galois (not `Ω/k`). -/
theorem fixingSubgroup_normal_of_isGalois' : (Λ.fixingSubgroup).Normal := by
  rw [← IntermediateField.restrictNormalHom_ker Λ]
  exact MonoidHom.normal_ker _

/-- Conjugation by any element of `G_k` preserves `G_Λ`. -/
theorem inv_mul_mul_mem_fixingSubgroup {τ u : Ω ≃ₐ[k] Ω} (hu : u ∈ Λ.fixingSubgroup) :
    τ⁻¹ * u * τ ∈ Λ.fixingSubgroup := by
  have hu' : AlgEquiv.restrictNormalHom Λ u = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker Λ]
    exact hu
  rw [← IntermediateField.restrictNormalHom_ker Λ, MonoidHom.mem_ker]
  show AlgEquiv.restrictNormalHom Λ (τ⁻¹ * u * τ) = 1
  rw [map_mul, map_mul, map_inv, hu']
  simp

/-- Conjugation by any element of `G_k` preserves `G_Λ` (the other order). -/
theorem mul_mul_inv_mem_fixingSubgroup {τ u : Ω ≃ₐ[k] Ω} (hu : u ∈ Λ.fixingSubgroup) :
    τ * u * τ⁻¹ ∈ Λ.fixingSubgroup := by
  have hu' : AlgEquiv.restrictNormalHom Λ u = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker Λ]
    exact hu
  rw [← IntermediateField.restrictNormalHom_ker Λ, MonoidHom.mem_ker]
  show AlgEquiv.restrictNormalHom Λ (τ * u * τ⁻¹) = 1
  rw [map_mul, map_mul, map_inv, hu']
  simp

end KillLambda

section TransferZero

variable {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)]
  {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]

/-- **The transfer vanishes on `G_Λ`** as soon as the cochain does.

For `δ ∈ Λ.fixingSubgroup` every conjugate `(sec s)⁻¹ δ sec s` again lies in `Λ.fixingSubgroup`
(normality of `G_Λ` in `G_k`), so every term of the transfer vanishes.  No additivity of `z` is
used. -/
theorem transfer_eq_zero_of_mem_fixingSubgroup
    {z : (Ω ≃ₐ[k] Ω) → E} {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)}
    (hzΛ : ∀ σ ∈ Λ.fixingSubgroup, z σ = 0) {δ : Ω ≃ₐ[k] Ω}
    (hδ : δ ∈ Λ.fixingSubgroup) :
    transfer z sec δ = 0 := by
  unfold transfer
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [hzΛ _ (inv_mul_mul_mem_fixingSubgroup (Λ := Λ) hδ), smul_zero]

/-- **The sixth conjunct of the node, with the explicit witness `V = G_Λ`**, at a place `B` split
in `Λ`, for a cochain `z` vanishing on `G_Λ`. -/
theorem exists_V_of_kills_fixingSubgroup
    (B : ValuationSubring Ω) (hsplitΛ : SSGRoute.IsSplitIn k Λ B)
    {z : (Ω ≃ₐ[k] Ω) → E} {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)}
    (hzΛ : ∀ σ ∈ Λ.fixingSubgroup, z σ = 0) :
    ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
      (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
      (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
      (∀ δ ∈ SSGRoute.decomp k B ⊓ V, transfer z sec δ = 0) := by
  refine ⟨Λ.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen Λ, ?_, ?_, ?_⟩
  · intro δ _ u hu
    exact mul_mul_inv_mem_fixingSubgroup (Λ := Λ) hu.2
  · refine ⟨1, Subgroup.one_mem _, fun δ hδ => ⟨0, ?_⟩⟩
    simpa using Λ.fixingSubgroup.inv_mem (hsplitΛ hδ)
  · intro δ hδ
    exact transfer_eq_zero_of_mem_fixingSubgroup hzΛ hδ.2

/-- **The node's sixth conjunct, in the form in which the node states it**
(unconditionally over the places outside `cs(S)` split in `Λ`), from a cochain vanishing on `G_Λ`. -/
theorem clause_six_of_kills_fixingSubgroup
    (S : Finset (ValuationSubring Ω))
    {z : (Ω ≃ₐ[k] Ω) → E} {sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)}
    (hzΛ : ∀ σ ∈ Λ.fixingSubgroup, z σ = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
      ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
        (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
        (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
        (∀ δ ∈ SSGRoute.decomp k B ⊓ V,
          (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0) := by
  intro B _ _ hsplitΛ
  exact exists_V_of_kills_fixingSubgroup B hsplitΛ hzΛ

/-- **The `z`-data (`Work.SSGRoute.HasZData`) from the five elementary clauses plus `z` killing
`G_Λ`.**

Schmidt–Wingberg's sharpened condition (b) — the sixth conjunct of `HasZData` — is triggered by
`z` being ramified at a place `B` split in `Λ`, i.e. by the existence of `σ ∈ I_B ⊓ G_K` with
`z σ ≠ 0`.  If `z` kills the whole subgroup `G_Λ` then `I_B ⊆ D_B ≤ G_Λ` for every `Λ`-split `B`,
so the trigger is false and condition (b) holds vacuously.  Consequently this route feeds the
`HasZData`-based induction of `ZConstruction/ZDataAux.lean` / `ZDataLevelStep.lean` directly. -/
theorem hasZData_of_kills_fixingSubgroup
    {S : Finset (ValuationSubring Ω)} {y z : (Ω ≃ₐ[k] Ω) → E}
    (h1 : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (h2 : SSGRoute.IsLocConstOn K.fixingSubgroup z)
    (h3 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ)
    (h4 : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0)
    (h5 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0)
    (h6 : ∀ σ ∈ Λ.fixingSubgroup, z σ = 0) :
    HasZData K Λ S y z := by
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro B hB _ hsplit htrig
  obtain ⟨σ, hσI, _hσK, hσne⟩ := htrig
  exact absurd (h6 σ (hsplit hσI.1)) hσne

end TransferZero

end Work.SSGRoute
