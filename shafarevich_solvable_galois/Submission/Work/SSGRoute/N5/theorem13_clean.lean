import Mathlib
import Submission.Work.SSGRoute.shafarevich_theorem13
import Submission.Work.SSGRoute.ZConstruction.MupCoreTwo
import Submission.Work.SSGRoute.ZConstruction.ZDataFinal
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.kummerCoreProved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A clean route to the `z`-construction (and to Theorem 13) at every prime

The node `Work.SSGRoute.shafarevich_existence` (Theorem 13 of Schmidt--Wingberg) is consumed by
`Work.SSGRoute.scholz_two_one` (and by the Step-4 lane) through the assembled atom
`Work.SSGRoute.z_data_general`, whose only open input was the `p = 2` Kummer core
(`Work.SSGRoute.ZDataTwo.mu2ThreeHalves`).  That core is now **proved**, in the lane
`Submission/Work/SSGRoute/NodeS37/mu2ThreeHalvesProved.lean`
(`Work.SSGRoute.NodeS37.mu2ThreeHalvesProved`, statement-identical to `mu2ThreeHalves`), and the
ZDataTwo lane re-pointed the Kummer core to it
(`Submission/Work/SSGRoute/ZDataTwo/TwoRec/kummerCoreProved.lean`,
`Work.SSGRoute.ZDataTwo.TwoRec.kummerCoreProved`).

The remaining obstruction to *using* that core from `shafarevich_z_data_two.lean` is an import
edge (`ZSplit/FrobeniusValue → shafarevich_z_data_two`, see
`ZDataTwo/PING_node_blocked_by_the_FrobeniusValue_import_edge.md`), which is irrelevant to the route
below: this file wires the `p = 2` core **directly** into

* the one-dimensional gate `Work.SSGRoute.IsMupZData 2 k Ω K` (`isMupZDataTwoClean`, a copy of
  `Work.SSGRoute.isMupZData_of_kummerCoreTwo`, `ZConstruction/MupCoreTwo.lean`, with the proved core
  in place of the `sorry`-carrying `Work.SSGRoute.shafarevich_z_data_two`), and
* the auxiliary-realisation gate of the §4 endgame (`auxRealisationGate_of_twoField` at `p = 2`,
  `auxRealisationGate_odd` at odd `p`),

and then runs the clean, `p`-generic wrappers
`Work.SSGRoute.z_data_general_of_realisationGate` and
`Work.SSGRoute.shafarevich_z_construction_of_realisationGate` — both axiom-clean — so that the
conclusion of the `z`-construction, and hence (via the axiom-clean bridge
`Work.SSGRoute.shafarevich_theorem13_of_z_construction`) the conclusion of Theorem 13, is available
with the *same* statement as `Work.SSGRoute.shafarevich_existence` at every prime `p`.

**Axiom footprint.**  Every declaration used here is axiom-clean except the proved `p = 2` core,
whose only remaining input is the single sub-lemma
`Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_diagonal`.  So the route below becomes clean as soon
as that one lemma lands, independently of the import-edge repair.
-/

namespace Work.SSGRoute.N5

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The one-dimensional gate `IsMupZData` at `p = 2`, from the proved `p = 2` core.**  Verbatim
`Work.SSGRoute.isMupZData_of_kummerCoreTwo` (`ZConstruction/MupCoreTwo.lean`) with its core input
`Work.SSGRoute.ZDataTwo.shafarevichZDataTwoKummerCoreH` replaced by the proved
`Work.SSGRoute.ZDataTwo.TwoRec.kummerCoreProved` (the same statement, with
`Work.SSGRoute.NodeS37.mu2ThreeHalvesProved` in place of the `sorry`-carrying
`Work.SSGRoute.ZDataTwo.mu2ThreeHalves`). -/
theorem isMupZDataTwoClean (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) :
    IsMupZData 2 k Ω K := by
  intro E _instE _instMod _instAct _instSMC _instFin h1 Λ _instΛf _instΛg hKΛ S hSfin hSdisj
    hSram y hy hyc hyS hyT hy0 hyinf
  haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  obtain ⟨z, hcoc, hloc, h3, h4, h5, h6⟩ :=
    shafarevich_z_data_two_of_kummerCore k Ω K Λ hKΛ ζ hζ hζK E h1 S hSfin hSdisj hSram y hy hyc
      hyS hyT hy0 hyinf
      (fun y' hy' hyc' hyS' hyT' hy0' hyinf' =>
        Work.SSGRoute.ZDataTwo.TwoRec.kummerCoreProved k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj hSram
          y' hy' hyc' hyS' hyT' hy0' hyinf')
  exact ⟨z, (isCocycleOn_fixingSubgroup_iff_additive z).mp hcoc, hloc, h3, h4, h5, h6⟩

/-- **The conclusion of the `z`-construction of Schmidt--Wingberg `§4` at every prime `p`**, from
the proved `p = 2` core.  The statement is character-identical to the conclusion of
`Work.SSGRoute.shafarevich_z_construction`; feeding it to
`Work.SSGRoute.shafarevich_theorem13_of_z_construction` (axiom-clean) yields Theorem 13 with the
statement of `Work.SSGRoute.shafarevich_existence`. -/
theorem zConstructionClean
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
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
  by_cases hp2 : p = 2
  · -- `p = 2`: the two-field narrow realisation carries the prime-`2` correction, and the
    -- one-dimensional gate is the proved `μ₂` core (`isMupZDataTwoClean`).
    subst hp2
    haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
    have hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (by simpa using hζ)
        (algebraMap ↥K Ω).injective
    have horthAll : Work.SSGRoute.ZConstruction.TwoFieldOrthogonalityAll (k := k) (Ω := Ω) K ζ hζ
        hζK hζK' :=
      Work.SSGRoute.ZConstruction.twoFieldOrthogonalityAll_of_orthHsplitTwoNarrow k Ω K ζ hζ hζK
        hζK'
    have hreal : Work.SSGRoute.ZConstruction.AuxRealisationGate (p := 2) (K := K) (ζ := ζ)
        (hζ := hζ) (hζK := hζK) :=
      Work.SSGRoute.ZConstruction.auxRealisationGate_of_twoField k Ω hζ hζK hζK' horthAll
    have hμ2 : IsMupZData 2 k Ω K := isMupZDataTwoClean k Ω K ζ hζ hζK
    exact shafarevich_z_construction_of_realisationGate 2 k Ω K Λ hKΛ ζ hζ hζK hreal hμ2 E S
      hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf sec hsec
  · -- odd `p`: the Grünwald-with-escape realisation and the `H9` lane's odd `μ_p` core.
    exact shafarevich_z_construction_of_isMupZData_odd p hp2 k Ω K Λ hKΛ ζ hζ hζK
      (isMupZData_of_kummerCore (p := p) (k := k) (Ω := Ω) (K := K) hp2 ζ hζ hζK) E S hSfin
      hSdisj hSram y hy hyc hyS hyT hy0 hyinf sec hsec

end Work.SSGRoute.N5
