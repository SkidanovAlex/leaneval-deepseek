import Submission.Work.SSGRoute.ZSplit.Assembly
import Submission.Work.SSGRoute.ZConstruction.ZDataGlue
import Submission.Work.SSGRoute.ZConstruction.ZDataBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The endgame wiring: the node from the two Grünwald-with-escape gates

The node `Work.SSGRoute.shafarevich_z_construction` is proved in its own file from the `z`-data
`Work.SSGRoute.z_data_general` (`ZConstruction/ZDataGeneral.lean`), whose single `sorry`
(`Work.SSGRoute.z_data_general_of_ramified`) is the shared arithmetic of §4.  Two *named* gate pairs
are known on disk which produce that `z`-data:

* the **Poitou--Tate** route: `Work.SSGRoute.MupGate` together with `Work.SSGRoute.AuxExists`
  (`Work.SSGRoute.z_data_general_of_ramified_of_gates`, `ZConstruction/ZDataGeneral.lean`), the
  latter reduced further to the pairing gate, the realisation `AuxRealisationT` and the no-gap
  provision (sessions 21--25);

* the **Grünwald-with-escape** route: `Work.SSGRoute.IsMupZData` (`A = μ_p`, the one-dimensional
  case at every pair `(Λ,S)`) together with `Work.SSGRoute.IsAuxiliaryZData` (the auxiliary class
  `ỹ` of §4 realised by the pairing-free relative Grünwald theorem
  `Work.SSGRoute.z_realisation_of_grunwald`, `zAux_of_grunwald.lean`).
  This is the route of `_NOTE_STEP4_DESIGN.md` §3, which replaces the (likely over-strong)
  realisation input `IsRealisationInput` by the escape-form Grünwald.

The present file performs the *second* wiring entirely inside the node's own import cone, so that
the endgame of the node is mechanical: once `IsMupZData` and `IsAuxiliaryZData` are available
without `sorry` (they are `Work.SSGRoute.z_data_mup_core` + `Work.SSGRoute.shafarevich_z_data_two`
and `Work.SSGRoute.isAuxiliaryZData_of_grunwald` respectively), the `sorry` of
`Work.SSGRoute.z_data_general_of_ramified` can be replaced by

    fun ... => hasZData_of_mup_and_aux (hμ) (haux) E Λ S hSfin hSdisj hSram y hy hyc hyS hyT hy0
      hyinf

and the node follows by the already-proved bridge `Work.SSGRoute.shafarevich_z_construction_of_zData`
(`ZConstruction/ZDataBridge.lean`).  The whole content of this file is the composition
`IsMupZData + IsAuxiliaryZData ⟹ IsZData` (`ZSplit/Assembly.lean`) with the definitional identity
`IsZData = HasZData` (`ZConstruction/ZDataRealisation.lean`); it is recorded separately because the
files that state the two gates live in the `ZSplit` subtree, which is under active edit by the
`Z` lane, whereas the node's cone must stay stable.

## Main results

* `Work.SSGRoute.ZConstruction.hasZData_of_mup_and_aux`
* `Work.SSGRoute.shafarevich_z_construction_of_mup_and_aux`
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)]
variable [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The `z`-data for an arbitrary finite coefficient module from the two Grünwald-with-escape
gates.**

`IsMupZData` is the one-dimensional case (`A = μ_p`) at every pair `(Λ,S)`; `IsAuxiliaryZData` is
the auxiliary-class input of the induction of §4, whose realisation is the pairing-free relative
Grünwald theorem `Work.SSGRoute.z_realisation_of_grunwald`.  Their combination gives the paper's
`z`-data `HasZData` at `(Λ,S)` for every finite coefficient module and every datum satisfying the
node's hypotheses. -/
theorem hasZData_of_mup_and_aux (hμ : IsMupZData p k Ω K) (haux : IsAuxiliaryZData p k Ω K) :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
      (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, IsFinPlace k A)
      (hSdisj : ∀ A ∈ S, ∀ B ∈ S, IsConjPlace k A B → A = B)
      (hSram : ∀ B : ValuationSubring Ω, IsFinPlace k B →
        (IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, IsConjPlace k A B)
      (y : (Ω ≃ₐ[k] Ω) → E)
      (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
      (hyc : IsLocConstOn K.fixingSubgroup y)
      (hyS : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
        ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0)
      (hyT : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0)
      (hy0 : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → y σ = 0)
      (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0),
      ∃ z, HasZData K Λ S y z := by
  intro E _instE _instM _instA _instC _instF Λ _ _ hKΛ S hSfin hSdisj hSram y hy hyc hyS hyT hy0
    hyinf
  obtain ⟨z, hz⟩ :=
    z_data_general_of_mup_and_aux_zsplit (p := p) (k := k) (Ω := Ω) (K := K) hμ haux E Λ hKΛ S
      hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf
  exact ⟨z, hz⟩

end Work.SSGRoute.ZConstruction

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedVariables false

/-- **The node `Work.SSGRoute.shafarevich_z_construction` from the two Grünwald-with-escape gates.**

This is the node's statement with `Work.SSGRoute.IsMupZData p k Ω K` (the one-dimensional gate) and
`Work.SSGRoute.IsAuxiliaryZData p k Ω K` (the auxiliary-class gate realised by the pairing-free
relative Grünwald theorem) added as hypotheses.  It is the drop-in shape for the endgame: both gates
are the objects the `Z` lane is closing (`Work.SSGRoute.isMupZData_of_workspace`, which reduces the
first to `Work.SSGRoute.z_data_mup_core` and `Work.SSGRoute.shafarevich_z_data_two`, and
`Work.SSGRoute.isAuxiliaryZData_of_grunwald`). -/
theorem shafarevich_z_construction_of_mup_and_aux
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hμ : IsMupZData p k Ω K) (haux : IsAuxiliaryZData p k Ω K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  obtain ⟨z, hz⟩ :=
    ZConstruction.hasZData_of_mup_and_aux (p := p) (k := k) (Ω := Ω) (K := K) hμ haux E Λ hKΛ S
      hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf
  exact shafarevich_z_construction_of_zData (K := K) (Λ := Λ) hKΛ S y sec hsec ⟨z, hz⟩

end Work.SSGRoute
