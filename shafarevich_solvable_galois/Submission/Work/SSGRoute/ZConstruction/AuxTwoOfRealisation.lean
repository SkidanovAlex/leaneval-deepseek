import Mathlib
import Submission.Work.SSGRoute.ZVocab
import Submission.Work.SSGRoute.ZRealV2.AuxOfGrunwaldV2
import Submission.Work.SSGRoute.ZConstruction.AuxRealisationGate
import Submission.Work.SSGRoute.ZConstruction.TwoFieldOrthogonality
import Submission.Work.SSGRoute.ZConstruction.RealisationTwoField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` auxiliary realisation from the `p = 2` Grünwald-with-escape realisation

`Work.SSGRoute.ZConstruction.auxRealisationGate_odd` instantiates the gate
`Work.SSGRoute.ZConstruction.AuxRealisationGate` at odd `p` from the proved realisation
`Work.SSGRoute.isAuxiliaryZData_of_grunwald_v2` (whose `hKimag` is available for odd `p`).

This file provides the *p = 2* instance, in the form in which the `p = 2` lane can supply it: the
gate is derived from the *realisation alone*, here taken as a hypothesis in the exact shape of

  `Work.SSGRoute.ZRealV2.z_realisation_of_grunwald_v2_own`

at `p = 2`, with `hKimag` deleted and the single extra hypothesis

  `hνinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → ν c = 0`

(the datum itself kills the involutions; in the node's application `ν = ρ ∘ y` and this is `hyinf`),
which is exactly the extra input the `p = 2` escape needs in place of `hKimag` (the escape element
must be totally positive, so that its Kummer cochain kills the involutions of `G_K`).

The proof is the proof of `Work.SSGRoute.isAuxiliaryZData_of_grunwald_v2`
(`Submission/Work/SSGRoute/ZRealV2/AuxOfGrunwaldV2.lean`), verbatim except for the realisation call:
nothing in it uses `hKimag`.  So the moment the `p = 2` realisation is on disk in the shape below,
the node's `p = 2` case closes through
`Work.SSGRoute.z_data_general_of_realisationGate` + `Work.SSGRoute.IsMupZData 2`
(no `AuxExists`, no Poitou--Tate input). -/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- **The `p = 2` instance of the gate**, from the `p = 2` realisation (taken as a hypothesis in the
shape of `Work.SSGRoute.ZRealV2.z_realisation_of_grunwald_v2_own` at `p = 2` without `hKimag`). -/
theorem auxRealisationGate_of_realisationTwo {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (hreal : ∀ (Λ L₂ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
        [FiniteDimensional k L₂] [IsGalois k L₂] (hKΛ : K ≤ Λ) (hKL₂ : K ≤ L₂)
        (S S₀ : Finset (ValuationSubring Ω)) (hSS₀ : S ⊆ S₀)
        (hS₀fin : ∀ A ∈ S₀, SSGRoute.IsFinPlace k A)
        (hS₀disj : ∀ A ∈ S₀, ∀ B ∈ S₀, SSGRoute.IsConjPlace k A B → A = B)
        (hS₀cov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (B.valuation (2 : Ω) < 1 ∨ SSGRoute.IsRamifiedIn k Λ B ∨
            SSGRoute.IsRamifiedIn k L₂ B) → ∃ A ∈ S₀, SSGRoute.IsConjPlace k A B)
        (hnew : ∀ A ∈ S₀, A ∉ S → SSGRoute.IsSplitIn k Λ A)
        (hL₂ : ∀ A ∈ S, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
          σ ∈ L₂.fixingSubgroup)
        (hL₂exp : ∀ σ ∈ K.fixingSubgroup, σ ^ 2 ∈ L₂.fixingSubgroup)
        (hL₂comm : ∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup,
          σ * τ * σ⁻¹ * τ⁻¹ ∈ L₂.fixingSubgroup)
        (ν : (Ω ≃ₐ[k] Ω) → ZMod 2),
        (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, ν (g * h) = ν g + ν h) →
        SSGRoute.IsLocConstOn K.fixingSubgroup ν →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → ν σ = 0) →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → ν σ = 0) →
        (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → ν c = 0) →
        ∃ yt : (Ω ≃ₐ[k] Ω) → ZMod 2,
          IsYRealisation 2 K (Λ ⊔ L₂) S S₀ (fun _ => ν) yt) :
    AuxRealisationGate (p := 2) (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) := by
  intro hgate Λ instΛf instΛg hKΛ Λ₀ instΛ₀f instΛ₀g hΛΛ₀ hKΛ₀ L instLf instLn hLΛ₀ S₀ hS₀ramL
    hS₀fin hS₀disj hS₀ramΛ₀ S hSfin hSsub hS₀new L₂ instL₂f instL₂g hKL₂ hΛL₂ hL₂exp hL₂comm
    hL₂iner hS₀ramΛ hS₀ramL₂ ν hadd hloc hνS hνT hν0 hνinf
  -- the auxiliary set covers the ramification of `L = L₂` and of `Λ`, so it covers the covering
  -- hypothesis of Grünwald with escape
  have hS₀cov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨ SSGRoute.IsRamifiedIn k Λ B ∨ SSGRoute.IsRamifiedIn k L₂ B) →
      ∃ A ∈ S₀, SSGRoute.IsConjPlace k A B := by
    intro B hB hc
    rcases hc with h | h | h
    · exact hS₀ramΛ₀ B hB (Or.inr h)
    · exact hS₀ramΛ B hB h
    · exact hS₀ramL₂ B hB h
  -- the `p = 2` realisation over `Λ ⊔ L₂`
  obtain ⟨yt, hyt0⟩ := hreal Λ L₂ hKΛ hKL₂ S S₀ hSsub hS₀fin hS₀disj hS₀cov hS₀new
    hL₂iner hL₂exp hL₂comm ν hadd hloc hνS hνT hνinf
  rw [hΛL₂] at hyt0
  -- a place conjugate to a place of `S` is a finite place
  have hfinplace : ∀ (A B : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      SSGRoute.IsConjPlace k A B → SSGRoute.IsFinPlace k B := by
    intro A B hA hAB
    obtain ⟨σ', hσ'⟩ := hAB
    rw [← hσ']
    exact (isFinPlace_smul_iff A σ').mpr hA
  -- the prescribed datum is unramified at the places of `S`
  have hfunr : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → (fun _ => ν) B σ = 0 := by
    intro B hB σ hσG hσI
    obtain ⟨A, hA, hAB⟩ := hB
    exact hνT B (hfinplace A B (hSfin A hA) hAB) ⟨A, hA, hAB⟩ σ hσG hσI
  -- and it vanishes on the local groups of the places of `S` over `2` or not split in `K`
  have hvanish : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → (fun _ => ν) B σ = 0 := by
    intro B hB hd σ hσG hσD
    obtain ⟨A, hA, hAB⟩ := hB
    exact hν0 B (hfinplace A B (hSfin A hA) hAB) ⟨A, hA, hAB⟩ hd σ hσG hσD
  -- hence the hypotheses of the one-dimensional statement for `yt`
  obtain ⟨hyS', hyT', hy0', hyinf'⟩ :=
    IsYRealisation.zStatementHypotheses 2 hyt0 hfunr hvanish
  -- `yt` is additive on `G_K`
  have hytadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, yt (g * h) = yt g + yt h := by
    intro g hg h hh
    have hres : res k K g = 1 := (res_eq_one_iff_mem_fixingSubgroup (K := K) g).mpr hg
    have hc := hyt0.1 g hg h hh
    rwa [hres, one_smul] at hc
  -- and the one-dimensional `z`-data for `yt` at the auxiliary pair
  obtain ⟨zF, hzF⟩ := hgate Λ₀ hKΛ₀ S₀ hS₀fin hS₀disj hS₀ramΛ₀ yt hytadd hyt0.2.1 hyS' hyT'
    hy0' hyinf'
  exact ⟨fun _ => ν, fun A hA => rfl, yt, zF, hyt0, hzF⟩

end Work.SSGRoute.ZConstruction

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

/-! ## The same instance from the two-field orthogonality gate

`Work.SSGRoute.z_realisation_of_grunwald_v2_two_field` (`ZConstruction/RealisationTwoField.lean`) is
the `p = 2` realisation with the orthogonality taken as the gate
`Work.SSGRoute.ZConstruction.TwoFieldOrthogonality` (instantiated by
`Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow`).  Below, the gate is quantified over the auxiliary
fields `Λ, L₂`, so that the instance of `AuxRealisationGate (p := 2)` is produced from the
orthogonality alone (plus the `p = 2` narrow escape of `ZConstruction/EscapeTwoField.lean`). -/

/-- **The two-field orthogonality gate, quantified over the auxiliary fields.** -/
def TwoFieldOrthogonalityAll (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2) : Prop :=
  ∀ (Λ L₂ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKΛ : K ≤ Λ) (hKL₂ : K ≤ L₂),
    TwoFieldOrthogonality (k := k) (Ω := Ω) K Λ L₂ hKΛ hKL₂ ζ hζ hζK hζK'

/-- **The `p = 2` instance of the gate, from the two-field orthogonality alone.** -/
theorem auxRealisationGate_of_twoField (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2)
    (horthAll : TwoFieldOrthogonalityAll (k := k) (Ω := Ω) K ζ hζ hζK hζK') :
    AuxRealisationGate (p := 2) (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) := by
  intro hgate Λ instΛf instΛg hKΛ Λ₀ instΛ₀f instΛ₀g hΛΛ₀ hKΛ₀ L instLf instLn hLΛ₀ S₀ hS₀ramL
    hS₀fin hS₀disj hS₀ramΛ₀ S hSfin hSsub hS₀new L₂ instL₂f instL₂g hKL₂ hΛL₂ hL₂exp hL₂comm
    hL₂iner hS₀ramΛ hS₀ramL₂ ν hadd hloc hνS hνT hν0 hνinf
  -- the three-way coverage of `T` for the realisation
  have hS₀cov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨ SSGRoute.IsRamifiedIn k Λ B ∨
        SSGRoute.IsRamifiedIn k L₂ B) → ∃ A ∈ S₀, SSGRoute.IsConjPlace k A B := by
    intro B hB hc
    rcases hc with h | h | h
    · exact hS₀ramΛ₀ B hB (Or.inr h)
    · exact hS₀ramΛ B hB h
    · exact hS₀ramL₂ B hB h
  -- the two-field `p = 2` realisation over `Λ ⊔ L₂ = Λ₀`
  obtain ⟨yt, hyt0⟩ := Work.SSGRoute.z_realisation_of_grunwald_v2_two_field (k := k) (Ω := Ω)
    (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) (hζK' := hζK') (Λ := Λ) (L₂ := L₂)
    (hKΛ := hKΛ) (hKL₂ := hKL₂) (S := S) (S₀ := S₀) (hSS₀ := hSsub) (hS₀fin := hS₀fin)
    (hS₀disj := hS₀disj) (hS₀cov := hS₀cov) (hnew := hS₀new) (hL₂ := hL₂iner)
    (hL₂exp := hL₂exp) (hL₂comm := hL₂comm) (ν := ν) (hν := hadd) (hνc := hloc)
    (hνS := hνS) (hνT := hνT) (hνinf := hνinf) (horth := horthAll Λ L₂ hKΛ hKL₂)
  rw [hΛL₂] at hyt0
  -- a place conjugate to a place of `S` is a finite place
  have hfinplace : ∀ (A B : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      SSGRoute.IsConjPlace k A B → SSGRoute.IsFinPlace k B := by
    intro A B hA hAB
    obtain ⟨σ', hσ'⟩ := hAB
    rw [← hσ']
    exact (isFinPlace_smul_iff A σ').mpr hA
  -- the prescribed datum is unramified at the places of `S`
  have hfunr : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → (fun _ => ν) B σ = 0 := by
    intro B hB σ hσG hσI
    obtain ⟨A, hA, hAB⟩ := hB
    exact hνT B (hfinplace A B (hSfin A hA) hAB) ⟨A, hA, hAB⟩ σ hσG hσI
  -- and it vanishes on the local groups of the places of `S` over `2` or not split in `K`
  have hvanish : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → (fun _ => ν) B σ = 0 := by
    intro B hB hd σ hσG hσD
    obtain ⟨A, hA, hAB⟩ := hB
    exact hν0 B (hfinplace A B (hSfin A hA) hAB) ⟨A, hA, hAB⟩ hd σ hσG hσD
  -- hence the hypotheses of the one-dimensional statement for `yt`
  obtain ⟨hyS', hyT', hy0', hyinf'⟩ :=
    IsYRealisation.zStatementHypotheses 2 hyt0 hfunr hvanish
  -- `yt` is additive on `G_K`
  have hytadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, yt (g * h) = yt g + yt h := by
    intro g hg h hh
    have hres : res k K g = 1 := (res_eq_one_iff_mem_fixingSubgroup (K := K) g).mpr hg
    have hc := hyt0.1 g hg h hh
    rwa [hres, one_smul] at hc
  -- and the one-dimensional `z`-data for `yt` at the auxiliary pair
  obtain ⟨zF, hzF⟩ := hgate Λ₀ hKΛ₀ S₀ hS₀fin hS₀disj hS₀ramΛ₀ yt hytadd hyt0.2.1 hyS' hyT'
    hy0' hyinf'
  exact ⟨fun _ => ν, fun A hA => rfl, yt, zF, hyt0, hzF⟩

end Work.SSGRoute.ZConstruction
