import Submission.NK.Reconstruct.levelIsoInput_of_localCorrespondence_complexPrime
import Submission.NK.EndgameRepair.LevelPairData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-pair bridge with a complex prime, on the **corrected** rank hypothesis

This is `NK.Reconstruct.levelIsoInput_of_localCorrespondence_complexPrime` — the complex-prime
half of Shimizu's Theorem 4.0 (arXiv:2009.10431 §4) — with the three `rankGamma`-inputs
`HausRankInput`, `RankStrictMonoLevelInputGen`, `ResRankInputGen` replaced by the single
hypothesis `NK.Reconstruct.Fourf5InputGen Ω ℓ`, which is the *only* way in which the original
proof used them (`NK.Reconstruct.fourf5_gen_of_rankInputs`).

The statement is `NK.EndgameRepair.LevelIsoInputOfFourf5 K₁ K₂ ℓ`
(`Submission/Work/EndgameRepair/LevelPairData.lean`).

The proof is the original proof verbatim: every ingredient (the level prime correspondence, the
`σbar` of the ℓ-adic abelianisations, the Frobenius correspondence at the level pair, the escaping
prime of Proposition 4f.3, the section `Θ`, the complex prime) is unchanged; only the derivation of
Proposition 4f.5 disappears, since it is now a hypothesis.

**Every on-disk theorem this file depends on is untouched** — in particular
`Submission/Work/Reconstruct/levelIsoInput_of_localCorrespondence_complexPrime.lean` is only
imported for its (public) helper lemmas, not edited.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.EndgameRepair

open scoped NumberField Pointwise
open NK.Reconstruct

attribute [local instance] NK.Reconstruct.NumFieldIn.finite
  NK.Reconstruct.NumFieldIn.numberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

set_option maxHeartbeats 8000000 in
theorem levelIsoInput_of_localCorrespondence_complexPrime_fourf5 {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] (K₁ K₂ : NK.Reconstruct.NumFieldIn ℚ Ω)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    NK.EndgameRepair.LevelIsoInputOfFourf5 K₁ K₂ ℓ := by
  classical
  intro ψ hψ a b hcomplex₀ h45 hc
  intro L hLfd
  -- ## Instances
  haveI hNfd : FiniteDimensional ↥K₂.L (levelMap ψ L) := finiteDimensional_levelMap hψ L
  haveI hNnf : NumberField ↥(levelMap ψ L) := numberField_levelMap hψ L
  haveI hLnf : NumberField ↥L := Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  haveI hsepL : IsSepClosure ↥L Ω := isSepClosure_level L
  haveI hsepN : IsSepClosure ↥(levelMap ψ L) Ω := isSepClosure_level (levelMap ψ L)
  -- ## The `ℚ`-levels of the two fields of the level pair
  let A : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₁ L
  let B : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₂ (levelMap ψ L)
  haveI hsepA : IsSepClosure ↥A.L Ω := isSepClosure_ofLevel K₁ L
  haveI hsepB : IsSepClosure ↥B.L Ω := isSepClosure_ofLevel K₂ (levelMap ψ L)
  -- ## An auxiliary finite Galois level of `Ω/ℚ` containing both
  obtain ⟨E, hAE, hBE⟩ := exists_frobLevel_sup A B
  haveI hsepE : IsSepClosure ↥E.L Ω := isSepClosure_of_le E.L
  -- ## The isomorphism `σbar` of ℓ-adic abelianisations induced by `ψ` at the level pair
  have hhomeo : IsHomeomorph (NK.ReconstructField.levelGalEquiv ψ hψ L) :=
    isHomeomorph_levelGalEquiv ψ hψ L
  obtain ⟨σbar, hσbar_cont, hσbar_compat, hσbar_compat_symm⟩ :=
    exists_gammaEquivOfPhi_continuous (NK.ReconstructField.levelGalEquiv ψ hψ L) hhomeo ℓ
  -- ## The prime correspondence of the level pair
  have hbij := NK.ReconstructField.levelPrimeMapGen_bijective ψ hψ a L
  let primeMap : NK.Chebotarev.PrimeIdeal ↥A.L ≃ NK.Chebotarev.PrimeIdeal ↥B.L :=
    Equiv.ofBijective _ hbij
  have hprimeMap (𝔭 : NK.Chebotarev.PrimeIdeal ↥A.L) :
      primeMap 𝔭 = NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭 :=
    Equiv.ofBijective_apply _ _ 𝔭
  -- ## The prime correspondence preserves the rational prime
  have hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥A.L,
      Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal := by
    intro 𝔭
    have hp : NK.LocalInputs.primeBelowNat ↥B.L (primeMap 𝔭) =
        NK.LocalInputs.primeBelowNat ↥A.L 𝔭 := by
      rw [hprimeMap 𝔭]
      exact NK.ReconstructField.primeBelowNat_levelPrimeMapGen ψ hψ a L 𝔭
    have hp' : NK.LocalInputs.primeBelow ↥B.L (primeMap 𝔭) =
        NK.LocalInputs.primeBelow ↥A.L 𝔭 :=
      Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext hp)
    rw [← Ideal.under_under (A := ℤ) (B := NumberField.RingOfIntegers ℚ)
        (C := NumberField.RingOfIntegers ↥B.L) (primeMap 𝔭).asIdeal,
      ← Ideal.under_under (A := ℤ) (B := NumberField.RingOfIntegers ℚ)
        (C := NumberField.RingOfIntegers ↥A.L) 𝔭.asIdeal,
      ← NK.LocalInputs.primeBelow_asIdeal ↥B.L (primeMap 𝔭),
      ← NK.LocalInputs.primeBelow_asIdeal ↥A.L 𝔭, hp']
  -- ## The Frobenius correspondence at the level pair
  have hb : ∀ (𝔭 : NK.Chebotarev.PrimeIdeal ↥A.L), SplitsCompletelyOverRat 𝔭 →
      ∀ (p : ℕ), CharP (NumberField.RingOfIntegers ↥A.L ⧸ 𝔭.asIdeal) p → p ≠ ℓ →
      ∀ (g₁ : Gal(Ω/↥A.L)) (g₂ : Gal(Ω/↥B.L)),
        IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ →
        gammaHausMk (K := ↥B.L) (K' := Ω) ℓ
            (σbar (galToGamma (K := ↥A.L) (K' := Ω) ℓ g₁)) =
          gammaHausMk (K := ↥B.L) (K' := Ω) ℓ
            (galToGamma (K := ↥B.L) (K' := Ω) ℓ g₂) := by
    intro 𝔭 hsplit p hpchar hpne g₁ g₂ hg₁ hg₂
    have hpb : CharP (NumberField.RingOfIntegers ↥A.L ⧸ 𝔭.asIdeal)
        (NK.LocalInputs.primeBelowNat ↥A.L 𝔭) :=
      NK.ReconstructField.charP_of_liesOver 𝔭 (NK.LocalInputs.primeBelow ↥A.L 𝔭)
        (NK.LocalInputs.primeBelow_liesOver ↥A.L 𝔭)
    have hprime : p.Prime := by
      rw [← CharP.eq _ hpb hpchar]
      exact (Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow ↥A.L 𝔭)).2
    haveI : Fact p.Prime := ⟨hprime⟩
    have hg2x : IsFrobElementAt (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭) g₂ :=
      show IsFrobElementAt (primeMap 𝔭) g₂ from hg₂
    have key := frobCorrespondenceGammaHaus_levelSplit ℓ ψ hψ a b L σbar
      hσbar_compat p 𝔭 hsplit hpchar hpne g₁ g₂ hg₁ hg2x
    exact key
  -- ## The escaping prime of Proposition 4f.3
  have hescape : ∀ (H : Gal(↥E.L/ℚ) → Subgroup (Gamma ↥E.L Ω ℓ)),
      (∀ i, IsClosed ((H i : Set (Gamma ↥E.L Ω ℓ)))) →
      (∀ i, ¬ IsOpen ((H i : Set (Gamma ↥E.L Ω ℓ)))) →
      ∃ (𝔭 : NK.Chebotarev.PrimeIdeal ↥E.L) (σ : Gal(Ω/↥E.L)),
        SplitsCompletelyOverRat 𝔭 ∧
        (∀ p : ℕ, CharP (NumberField.RingOfIntegers ↥E.L ⧸ 𝔭.asIdeal) p → p ≠ ℓ) ∧
        IsFrobElementAt 𝔭 σ ∧ ∀ i, galToGamma (K := ↥E.L) (K' := Ω) ℓ σ ∉ H i := by
    intro H hcl hopen
    haveI : Finite (Gal(↥E.L/ℚ)) := inferInstance
    obtain ⟨𝔭, σ, hfrob, hsplit, hpne, hout⟩ :=
      exists_splitIsFrobElementAt_notMem_iUnion_closedSubgroup_awayFromL hc E ℓ H hcl hopen
    refine ⟨𝔭, σ, hsplit, ?_, hfrob, hout⟩
    intro p hpchar
    have hpb : CharP (NumberField.RingOfIntegers ↥E.L ⧸ 𝔭.asIdeal)
        (NK.LocalInputs.primeBelowNat ↥E.L 𝔭) :=
      NK.ReconstructField.charP_of_liesOver 𝔭 (NK.LocalInputs.primeBelow ↥E.L 𝔭)
        (NK.LocalInputs.primeBelow_liesOver ↥E.L 𝔭)
    rw [← CharP.eq _ hpb hpchar]
    exact hpne
  -- ## The section `Θ` of the restriction `Gal(Ω/ℚ) → Gal(E.L/ℚ)`
  haveI hEfin := E.finite
  haveI hEnorm : Normal ℚ ↥E.L := by
    have he : (E.L.algebra' : Algebra ℚ ↥E.L) = (inferInstance : Algebra ℚ ↥E.L) :=
      Subsingleton.elim _ _
    exact Eq.mp (congrArg (fun a : Algebra ℚ ↥E.L => @Normal ℚ ↥E.L _ _ a) he) E.normal
  let Θ : Gal(↥E.L/ℚ) → Ω ≃ₐ[ℚ] Ω :=
    fun τ => (exists_algEquiv_extends E.L τ).choose
  have hΘmem : ∀ τ, ∀ x : Ω, x ∈ E.L ↔ Θ τ x ∈ E.L :=
    fun τ => (exists_algEquiv_extends E.L τ).choose_spec.1
  have hΘres : ∀ τ (x : ↥E.L), Θ τ (x : Ω) = ((τ x : ↥E.L) : Ω) :=
    fun τ x => (exists_algEquiv_extends E.L τ).choose_spec.2 x
  -- ## Shimizu's Proposition 4f.3 gives the `τ` of the theorem
  obtain ⟨τ, hτ⟩ := prop4f3_awayFromL A B E hAE hBE ℓ σbar hσbar_cont primeMap hb hchar
    (fun τ => (Θ τ : Ω ≃+* Ω)) (fun τ => hΘmem τ) (fun τ x => hΘres τ x) hescape
  have hprop : ∃ τ : Gal(↥E.L/ℚ), ∀ γ : Gamma ↥E.L Ω ℓ,
      gammaHausMk (K := ↥B.L) (K' := Ω) ℓ (σbar (ambientPi A E hAE ℓ γ)) =
        gammaHausMk (K := ↥B.L) (K' := Ω) ℓ
          (ambientPi B E hBE ℓ
            (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)) := ⟨τ, hτ⟩
  -- ## The complex prime, inherited by the level `L`
  have hcomplex : ∃ v : NumberField.InfinitePlace ↥A.L, NumberField.InfinitePlace.IsComplex v :=
    numberField_complex_of_le K₁ A (NumFieldIn.le_ofLevel K₁ L) hcomplex₀
  -- ## The corrected rank hypothesis: Shimizu's Proposition 4f.5 is the hypothesis `h45`
  -- ## Shimizu's Theorem 4.0 (the assembly)
  obtain ⟨τ', hne⟩ := exists_isomorphism_of_prop4f3_data_gen_awayFromL A B E hAE hBE ℓ σbar
    hσbar_cont Θ hΘmem hΘres hprop hcomplex h45
  exact hne

end NK.EndgameRepair
