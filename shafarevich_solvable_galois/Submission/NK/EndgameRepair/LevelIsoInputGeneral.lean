import Submission.NK.Reconstruct.levelIsoInput_of_localCorrespondence
import Submission.NK.EndgameRepair.LevelIsoInputComplexPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-pair bridge of the Shimizu endgame, on the **corrected** rank hypothesis

This is `NK.Reconstruct.levelIsoInput_of_localCorrespondence` — Shimizu's Theorem 4.0
(arXiv:2009.10431 §4) in full generality, i.e. *without* the complex-prime hypothesis of
Proposition 4f.5, obtained by the totally imaginary twist — with the three `rankGamma`-inputs
`HausRankInput`, `RankStrictMonoLevelInputGen`, `ResRankInputGen` replaced by the single
hypothesis `NK.Reconstruct.Fourf5InputGen Ω ℓ` (Shimizu's Proposition 4f.5).

The statement is `NK.EndgameRepair.LevelIsoInputOfCorrespondenceFourf5 K₁ K₂ ℓ`
(`Submission/Work/EndgameRepair/LevelPairData.lean`).

The proof is the original proof verbatim: its complex-prime case is delegated to
`NK.EndgameRepair.levelIsoInput_of_localCorrespondence_complexPrime_fourf5`, and in the
totally-imaginary twist case the only change is that Proposition 4f.5 is the hypothesis `h45`
rather than `NK.Reconstruct.fourf5_gen_of_rankInputs ℓ hH hM hR`.  Everything else — the two
auxiliary imaginary quadratic fields, the base-change compatibility square
`NK.Reconstruct.sigmaBar_compat_gen`, the descent of Shimizu's Proposition 4f.3 identity to the
sub-pairs (`NK.Reconstruct.prop4f3_identity_of_le_gen`), the escaping prime, the section `Θ`,
and the intersection argument — is the on-disk proof, imported unchanged.
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

theorem levelIsoInput_of_localCorrespondence_fourf5 {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] (K₁ K₂ : NK.Reconstruct.NumFieldIn ℚ Ω)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    NK.EndgameRepair.LevelIsoInputOfCorrespondenceFourf5 K₁ K₂ ℓ := by
  intro ψ hψ a b h45 hc L hLfd
  by_cases hcomplex : ∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v
  · exact levelIsoInput_of_localCorrespondence_complexPrime_fourf5 K₁ K₂ ℓ ψ hψ a b hcomplex h45 hc L
  · -- ## Case 2: `K₁` has no complex prime — the totally imaginary twist
    classical
    -- ## instances at the level `L` and at its image
    haveI hNfd : FiniteDimensional ↥K₂.L (levelMap ψ L) := finiteDimensional_levelMap hψ L
    haveI hNnf : NumberField ↥(levelMap ψ L) := numberField_levelMap hψ L
    haveI hLnf : NumberField ↥L :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField L
    haveI hsepL : IsSepClosure ↥L Ω := isSepClosure_level L
    haveI hsepN : IsSepClosure ↥(levelMap ψ L) Ω := isSepClosure_level (levelMap ψ L)
    -- ## the two auxiliary imaginary quadratic extensions of `L`
    obtain ⟨i, y, q, hi, hy, hqpos, hinf⟩ := exists_aux_imaginary_level_gen K₁ L
    -- ## the enlarged levels over `↥K₁.L`
    haveI hfdi : FiniteDimensional ↥K₁.L (IntermediateField.adjoin ↥K₁.L ({i} : Set Ω)) :=
      IntermediateField.adjoin.finiteDimensional
        ⟨Polynomial.X ^ 2 + Polynomial.C 1, Polynomial.monic_X_pow_add_C (1 : ↥K₁.L) (by norm_num),
          by simp [hi]⟩
    haveI hfdy : FiniteDimensional ↥K₁.L (IntermediateField.adjoin ↥K₁.L ({y} : Set Ω)) :=
      IntermediateField.adjoin.finiteDimensional
        ⟨Polynomial.X ^ 2 + Polynomial.C (q : ↥K₁.L),
          Polynomial.monic_X_pow_add_C (q : ↥K₁.L) (by norm_num), by simp [hy]⟩
    let l₁ : IntermediateField ↥K₁.L Ω := L ⊔ IntermediateField.adjoin ↥K₁.L ({i} : Set Ω)
    let l₁' : IntermediateField ↥K₁.L Ω := L ⊔ IntermediateField.adjoin ↥K₁.L ({y} : Set Ω)
    haveI hl₁fd : FiniteDimensional ↥K₁.L l₁ := IntermediateField.finiteDimensional_sup L _
    haveI hl₁'fd : FiniteDimensional ↥K₁.L l₁' := IntermediateField.finiteDimensional_sup L _
    haveI hl₁nf : NumberField ↥l₁ :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField l₁
    haveI hl₁'nf : NumberField ↥l₁' :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField l₁'
    haveI hfd₁ : FiniteDimensional ↥K₂.L (levelMap ψ l₁) := finiteDimensional_levelMap hψ l₁
    haveI hfd₁' : FiniteDimensional ↥K₂.L (levelMap ψ l₁') := finiteDimensional_levelMap hψ l₁'
    haveI hnf₁ : NumberField ↥(levelMap ψ l₁) := numberField_levelMap hψ l₁
    haveI hnf₁' : NumberField ↥(levelMap ψ l₁') := numberField_levelMap hψ l₁'
    haveI hsepL₁ : IsSepClosure ↥l₁ Ω := isSepClosure_level l₁
    haveI hsepL₁' : IsSepClosure ↥l₁' Ω := isSepClosure_level l₁'
    haveI hsepl₁ : IsSepClosure ↥(levelMap ψ l₁) Ω := isSepClosure_level (levelMap ψ l₁)
    haveI hsepl₁' : IsSepClosure ↥(levelMap ψ l₁') Ω := isSepClosure_level (levelMap ψ l₁')
    -- ## the `NumFieldIn`s of the twisted pairs
    let A₁ : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₁ l₁
    let A₁' : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₁ l₁'
    let B₁ : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₂ (levelMap ψ l₁)
    let B₁' : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₂ (levelMap ψ l₁')
    let m₁ : IntermediateField ↥K₁.L Ω := l₁ ⊔ l₁'
    haveI hm₁fd : FiniteDimensional ↥K₁.L m₁ := IntermediateField.finiteDimensional_sup l₁ l₁'
    haveI hm₁nf : NumberField ↥m₁ :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField m₁
    haveI hfdm : FiniteDimensional ↥K₂.L (levelMap ψ m₁) := finiteDimensional_levelMap hψ m₁
    haveI hnflm : NumberField ↥(levelMap ψ m₁) := numberField_levelMap hψ m₁
    haveI hsepM : IsSepClosure ↥m₁ Ω := isSepClosure_level m₁
    haveI hseplm : IsSepClosure ↥(levelMap ψ m₁) Ω := isSepClosure_level (levelMap ψ m₁)
    let M₁ : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₁ m₁
    let M₂ : NumFieldIn ℚ Ω := NumFieldIn.ofLevel K₂ (levelMap ψ m₁)
    -- ## the inclusions of the underlying `ℚ`-levels
    have hl₁m₁ : l₁ ≤ m₁ := le_sup_left
    have hl₁'m₁ : l₁' ≤ m₁ := le_sup_right
    have hA₁M₁ : A₁.L ≤ M₁.L := hl₁m₁
    have hA₁'M₁ : A₁'.L ≤ M₁.L := hl₁'m₁
    have hB₁M₂ : B₁.L ≤ M₂.L := NK.ReconstructField.levelMap_monotone ψ hl₁m₁
    have hB₁'M₂ : B₁'.L ≤ M₂.L := NK.ReconstructField.levelMap_monotone ψ hl₁'m₁
    -- ## an auxiliary finite Galois level of `Ω/ℚ` containing everything
    obtain ⟨E, hM₁E, hM₂E⟩ := exists_frobLevel_sup M₁ M₂
    haveI hsepE : IsSepClosure ↥E.L Ω := isSepClosure_of_le E.L
    have hA₁E : A₁.L ≤ E.L := le_trans hA₁M₁ hM₁E
    have hA₁'E : A₁'.L ≤ E.L := le_trans hA₁'M₁ hM₁E
    have hB₁E : B₁.L ≤ E.L := le_trans hB₁M₂ hM₂E
    have hB₁'E : B₁'.L ≤ E.L := le_trans hB₁'M₂ hM₂E
    -- ## separability of everything
    haveI hsepA₁ : IsSepClosure ↥A₁.L Ω := isSepClosure_ofLevel K₁ l₁
    haveI hsepA₁' : IsSepClosure ↥A₁'.L Ω := isSepClosure_ofLevel K₁ l₁'
    haveI hsepB₁ : IsSepClosure ↥B₁.L Ω := isSepClosure_ofLevel K₂ (levelMap ψ l₁)
    haveI hsepB₁' : IsSepClosure ↥B₁'.L Ω := isSepClosure_ofLevel K₂ (levelMap ψ l₁')
    haveI hsepM₁ : IsSepClosure ↥M₁.L Ω := isSepClosure_ofLevel K₁ m₁
    haveI hsepM₂ : IsSepClosure ↥M₂.L Ω := isSepClosure_ofLevel K₂ (levelMap ψ m₁)
    -- ## the isomorphisms `σ̄` of the ℓ-adic abelianisations of the three pairs
    obtain ⟨σbar₁, hσbar₁cont, hσbar₁compat, -⟩ :=
      exists_gammaEquivOfPhi_continuous (NK.ReconstructField.levelGalEquiv ψ hψ l₁)
        (isHomeomorph_levelGalEquiv ψ hψ l₁) ℓ
    obtain ⟨σbar₁', hσbar₁'cont, hσbar₁'compat, -⟩ :=
      exists_gammaEquivOfPhi_continuous (NK.ReconstructField.levelGalEquiv ψ hψ l₁')
        (isHomeomorph_levelGalEquiv ψ hψ l₁') ℓ
    obtain ⟨σbarM, hσbarMcont, hσbarMcompat, -⟩ :=
      exists_gammaEquivOfPhi_continuous (NK.ReconstructField.levelGalEquiv ψ hψ m₁)
        (isHomeomorph_levelGalEquiv ψ hψ m₁) ℓ
    -- ## the prime correspondence and the Frobenius correspondence of the large pair
    have hbij := NK.ReconstructField.levelPrimeMapGen_bijective ψ hψ a m₁
    let primeMap : NK.Chebotarev.PrimeIdeal ↥M₁.L ≃ NK.Chebotarev.PrimeIdeal ↥M₂.L :=
      Equiv.ofBijective _ hbij
    have hprimeMap (𝔭 : NK.Chebotarev.PrimeIdeal ↥M₁.L) :
        primeMap 𝔭 = NK.ReconstructField.levelPrimeMapGen ψ hψ a m₁ 𝔭 :=
      Equiv.ofBijective_apply _ _ 𝔭
    have hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥M₁.L,
        Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal := by
      intro 𝔭
      have hp : NK.LocalInputs.primeBelowNat ↥M₂.L (primeMap 𝔭) =
          NK.LocalInputs.primeBelowNat ↥M₁.L 𝔭 := by
        rw [hprimeMap 𝔭]
        exact NK.ReconstructField.primeBelowNat_levelPrimeMapGen ψ hψ a m₁ 𝔭
      have hp' : NK.LocalInputs.primeBelow ↥M₂.L (primeMap 𝔭) =
          NK.LocalInputs.primeBelow ↥M₁.L 𝔭 :=
        Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext hp)
      rw [← Ideal.under_under (A := ℤ) (B := NumberField.RingOfIntegers ℚ)
          (C := NumberField.RingOfIntegers ↥M₂.L) (primeMap 𝔭).asIdeal,
        ← Ideal.under_under (A := ℤ) (B := NumberField.RingOfIntegers ℚ)
          (C := NumberField.RingOfIntegers ↥M₁.L) 𝔭.asIdeal,
        ← NK.LocalInputs.primeBelow_asIdeal ↥M₂.L (primeMap 𝔭),
        ← NK.LocalInputs.primeBelow_asIdeal ↥M₁.L 𝔭, hp']
    have hb : ∀ (𝔭 : NK.Chebotarev.PrimeIdeal ↥M₁.L), SplitsCompletelyOverRat 𝔭 →
        ∀ (p : ℕ), CharP (NumberField.RingOfIntegers ↥M₁.L ⧸ 𝔭.asIdeal) p → p ≠ ℓ →
        ∀ (g₁ : Gal(Ω/↥M₁.L)) (g₂ : Gal(Ω/↥M₂.L)),
          IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ →
          gammaHausMk (K := ↥M₂.L) (K' := Ω) ℓ
              (σbarM (galToGamma (K := ↥M₁.L) (K' := Ω) ℓ g₁)) =
            gammaHausMk (K := ↥M₂.L) (K' := Ω) ℓ
              (galToGamma (K := ↥M₂.L) (K' := Ω) ℓ g₂) := by
      intro 𝔭 hsplit p hpchar hpne g₁ g₂ hg₁ hg₂
      have hpb : CharP (NumberField.RingOfIntegers ↥M₁.L ⧸ 𝔭.asIdeal)
          (NK.LocalInputs.primeBelowNat ↥M₁.L 𝔭) :=
        NK.ReconstructField.charP_of_liesOver 𝔭 (NK.LocalInputs.primeBelow ↥M₁.L 𝔭)
          (NK.LocalInputs.primeBelow_liesOver ↥M₁.L 𝔭)
      have hprime : p.Prime := by
        rw [← CharP.eq _ hpb hpchar]
        exact (Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow ↥M₁.L 𝔭)).2
      haveI : Fact p.Prime := ⟨hprime⟩
      have hg2x : IsFrobElementAt (NK.ReconstructField.levelPrimeMapGen ψ hψ a m₁ 𝔭) g₂ :=
        show IsFrobElementAt (primeMap 𝔭) g₂ from hg₂
      exact frobCorrespondenceGammaHaus_levelSplit ℓ ψ hψ a b m₁ σbarM hσbarMcompat p 𝔭 hsplit
        hpchar hpne g₁ g₂ hg₁ hg2x
    -- ## the escaping prime of Proposition 4f.3
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
    -- ## the section `Θ` of the restriction `Gal(Ω/ℚ) → Gal(E.L/ℚ)`
    haveI hEfin := E.finite
    haveI hEnorm : Normal ℚ ↥E.L := by
      have he : (E.L.algebra' : Algebra ℚ ↥E.L) = (inferInstance : Algebra ℚ ↥E.L) :=
        Subsingleton.elim _ _
      exact Eq.mp (congrArg (fun a : Algebra ℚ ↥E.L => @Normal ℚ ↥E.L _ _ a) he) E.normal
    let Θ : Gal(↥E.L/ℚ) → Ω ≃ₐ[ℚ] Ω := fun τ => (exists_algEquiv_extends E.L τ).choose
    have hΘmem : ∀ τ, ∀ x : Ω, x ∈ E.L ↔ Θ τ x ∈ E.L :=
      fun τ => (exists_algEquiv_extends E.L τ).choose_spec.1
    have hΘres : ∀ τ (x : ↥E.L), Θ τ (x : Ω) = ((τ x : ↥E.L) : Ω) :=
      fun τ x => (exists_algEquiv_extends E.L τ).choose_spec.2 x
    -- ## Shimizu's Proposition 4f.3 at the large pair
    obtain ⟨τ, hτM⟩ := prop4f3_awayFromL M₁ M₂ E hM₁E hM₂E ℓ σbarM hσbarMcont primeMap hb hchar
      (fun τ => (Θ τ : Ω ≃+* Ω)) (fun τ => hΘmem τ) (fun τ x => hΘres τ x) hescape
    -- ## the same identity at the two sub-pairs, with the same `τ`
    have hτ₁ : ∀ γ : Gamma ↥E.L Ω ℓ,
        gammaHausMk (K := ↥(levelMap ψ l₁)) (K' := Ω) ℓ (σbar₁ (ambientPi A₁ E hA₁E ℓ γ))
          = gammaHausMk (K := ↥(levelMap ψ l₁)) (K' := Ω) ℓ
              (ambientPi B₁ E hB₁E ℓ (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)) :=
      prop4f3_identity_of_le_gen K₁ K₂ ψ hψ ℓ (A := l₁) (M := m₁) hl₁m₁ E hA₁E hM₁E hB₁E hM₂E
        Θ hΘmem τ σbar₁ σbarM hσbar₁compat hσbarMcompat hτM
    have hτ₁' : ∀ γ : Gamma ↥E.L Ω ℓ,
        gammaHausMk (K := ↥(levelMap ψ l₁')) (K' := Ω) ℓ (σbar₁' (ambientPi A₁' E hA₁'E ℓ γ))
          = gammaHausMk (K := ↥(levelMap ψ l₁')) (K' := Ω) ℓ
              (ambientPi B₁' E hB₁'E ℓ (tauStar E.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)) :=
      prop4f3_identity_of_le_gen K₁ K₂ ψ hψ ℓ (A := l₁') (M := m₁) hl₁'m₁ E hA₁'E hM₁E hB₁'E hM₂E
        Θ hΘmem τ σbar₁' σbarM hσbar₁'compat hσbarMcompat hτM
    -- ## the complex primes of the twisted fields
    have hi_l₁ : i ∈ l₁ := by
      have hle : IntermediateField.adjoin ↥K₁.L ({i} : Set Ω) ≤ l₁ := le_sup_right
      exact hle (IntermediateField.subset_adjoin ↥K₁.L ({i} : Set Ω) (by simp))
    have hy_l₁' : y ∈ l₁' := by
      have hle : IntermediateField.adjoin ↥K₁.L ({y} : Set Ω) ≤ l₁' := le_sup_right
      exact hle (IntermediateField.subset_adjoin ↥K₁.L ({y} : Set Ω) (by simp))
    have hi_A₁ : i ∈ A₁.L := hi_l₁
    have hy_A₁' : y ∈ A₁'.L := hy_l₁'
    have hi_M₁ : i ∈ M₁.L := by
      have hle : l₁ ≤ m₁ := le_sup_left
      exact hle hi_l₁
    have hcomplexA₁ : ∃ v : NumberField.InfinitePlace ↥A₁.L,
        NumberField.InfinitePlace.IsComplex v :=
      exists_isComplex_of_sq_eq_neg_one_gen ↥A₁.L (i := ⟨i, hi_A₁⟩) (by
        apply Subtype.ext
        push_cast
        exact hi)
    have hcomplexA₁' : ∃ v : NumberField.InfinitePlace ↥A₁'.L,
        NumberField.InfinitePlace.IsComplex v :=
      exists_isComplex_of_sq_eq_neg_gen ↥A₁'.L (w := ⟨y, hy_A₁'⟩) (q := (q : ℚ))
        (by exact_mod_cast hqpos) (by
          apply Subtype.ext
          push_cast
          exact hy)
    have hcomplexM₁ : ∃ v : NumberField.InfinitePlace ↥M₁.L,
        NumberField.InfinitePlace.IsComplex v :=
      exists_isComplex_of_sq_eq_neg_one_gen ↥M₁.L (i := ⟨i, hi_M₁⟩) (by
        apply Subtype.ext
        push_cast
        exact hi)
    -- ## Shimizu's Theorem 4.0 at the two sub-pairs
    have hEq₁ : A₁.L = B₁.L.map (Θ τ).symm.toAlgHom :=
      exists_theta_of_prop4f3_data_gen_awayFromL_fixed A₁ B₁ E hA₁E hB₁E ℓ σbar₁ hσbar₁cont
        Θ hΘmem (fun τ x => hΘres τ x) τ hτ₁ hcomplexA₁ h45
    have hEq₁' : A₁'.L = B₁'.L.map (Θ τ).symm.toAlgHom :=
      exists_theta_of_prop4f3_data_gen_awayFromL_fixed A₁' B₁' E hA₁'E hB₁'E ℓ σbar₁' hσbar₁'cont
        Θ hΘmem (fun τ x => hΘres τ x) τ hτ₁' hcomplexA₁' h45
    -- ## the intersection: `L = τ(levelMap ψ L)`
    have hfin : l₁ ⊓ l₁' = L := hinf
    have hAinf : A₁.L ⊓ A₁'.L = (NumFieldIn.ofLevel K₁ L).L := by
      refine le_antisymm ?_ ?_
      · intro x hx
        rw [IntermediateField.mem_inf] at hx
        have hx' : x ∈ l₁ ⊓ l₁' := by
          rw [IntermediateField.mem_inf]
          exact ⟨hx.1, hx.2⟩
        rw [hinf] at hx'
        exact hx'
      · intro x hx
        have hxL : x ∈ L := hx
        have hxl₁ : x ∈ l₁ := (le_sup_left : L ≤ l₁) hxL
        have hxl₁' : x ∈ l₁' := (le_sup_left : L ≤ l₁') hxL
        rw [IntermediateField.mem_inf]
        exact ⟨hxl₁, hxl₁'⟩
    have hXeq : B₁.L ⊓ B₁'.L = (NumFieldIn.ofLevel K₂ (levelMap ψ L)).L := by
      have hlinf : levelMap ψ (l₁ ⊓ l₁') = levelMap ψ l₁ ⊓ levelMap ψ l₁' :=
        levelMap_inf K₁ K₂ ψ hψ l₁ l₁'
      refine le_antisymm ?_ ?_
      · intro x hx
        rw [IntermediateField.mem_inf] at hx
        have hx' : x ∈ levelMap ψ l₁ ⊓ levelMap ψ l₁' := by
          rw [IntermediateField.mem_inf]
          exact ⟨hx.1, hx.2⟩
        rw [← hlinf, hfin] at hx'
        exact hx'
      · intro x hx
        have hx' : x ∈ levelMap ψ l₁ ⊓ levelMap ψ l₁' := by
          rw [← hlinf, hfin]
          exact hx
        rw [IntermediateField.mem_inf] at hx'
        exact ⟨hx'.1, hx'.2⟩
    -- ## the field isomorphism of the level pair
    have hmapinf : (B₁.L ⊓ B₁'.L).map (Θ τ).symm.toAlgHom = A₁.L ⊓ A₁'.L := by
      rw [IntermediateField.map_inf (B₁.L) (B₁'.L) (Θ τ).symm.toAlgHom, ← hEq₁, ← hEq₁']
    have hmain : Nonempty
        (↥((B₁.L ⊓ B₁'.L).map (Θ τ).symm.toAlgHom) ≃+* ↥(B₁.L ⊓ B₁'.L)) := by
      letI : Algebra ℚ ↥(B₁.L ⊓ B₁'.L) := (B₁.L ⊓ B₁'.L).algebra'
      letI : Algebra ℚ ↥((B₁.L ⊓ B₁'.L).map (Θ τ).symm.toAlgHom) :=
        ((B₁.L ⊓ B₁'.L).map (Θ τ).symm.toAlgHom).algebra'
      exact ⟨(IntermediateField.equivMap (B₁.L ⊓ B₁'.L) (Θ τ).symm.toAlgHom).symm.toRingEquiv⟩
    rw [hmapinf, hAinf, hXeq] at hmain
    exact hmain

end NK.EndgameRepair
