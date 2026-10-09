import Submission.NeukirchUchida.Endgame
import Submission.NK.BrauerHasse.All
import Submission.NK.Mine.preservesDecompositionGroups_of_localGalois
import Submission.NK.FrobeniusBridge.Endgame
import Submission.NK.LocalCFT.All
import Submission.NK.LocalInputs.AbelianRank.hasAbelianFrattiniRank_of_maxAbelian_of_isOpen
import Submission.NK.LocalInputs.Global
import Submission.NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime
import Submission.NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The arithmetic fields of the place correspondence (input (a)) of Neukirch–Uchida

`Submission.NeukirchUchida.localCorrespondenceOf` builds the place correspondence
`NK.Reconstruct.LocalCorrespondence ϕ` from

* the group-theoretic input `PreservesDecompositionGroups ϕ` (CoNF (12.1.9) "if"), and
* two *arithmetic* fields: corresponding primes have the same residue characteristic and the same
  absolute local degree.

This file proves those two arithmetic fields from the local structure theory of the completions
(`NK.LocalInputs.LocalFieldInputs` and `NK.LocalInputs.LocalGaloisInputs`, i.e. the arithmetic of
`κˣ` and the local reciprocity computation of `G_κ^{ab}`), and assembles the whole of input (a).

The mathematical content is `NK.LocalInputs.primeBelow_and_localDegree_eq_of_decompositionGroup`:
two completions whose decomposition groups correspond have the same residue characteristic and the
same absolute degree.  Here it is transported to the vocabulary of `primeOf` (the finite prime of the
number field below a place) and of `localCorrespondenceOf`.
-/

namespace NK.Mine

open scoped Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **`CharP` transfers along a ring equivalence.** -/
theorem charP_of_ringEquiv {R S : Type*} [NonAssocRing R] [NonAssocRing S] (e : R ≃+* S) {p : ℕ}
    [CharP R p] : CharP S p :=
  charP_of_injective_ringHom (f := (e : R →+* S)) e.injective p

/-- The residue field of the completion `𝒪_{K_𝔭}` is the residue field `𝓞 K ⧸ 𝔭` of `𝔭`, so
`CharP` transfers between them. -/
theorem charP_residueField_iff {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (p : ℕ) :
    CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p ↔
      CharP (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) p := by
  obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists 𝔭
  exact ⟨fun h => @charP_of_ringEquiv _ _ _ _ e p h, fun h => @charP_of_ringEquiv _ _ _ _ e.symm p h⟩

/-- **The residue characteristic is preserved by the place correspondence.**

Given the local structure inputs at every finite prime of both fields and the group-theoretic input
`PreservesDecompositionGroups ϕ`, the primes below corresponding places have residue fields of the
same characteristic. -/
theorem residueChar_preserved_of_localInputs
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p ∧
        NK.LocalInputs.LocalGaloisInputs K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q ∧
        NK.LocalInputs.LocalGaloisInputs K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q) :
    ∀ (A : NK.Reconstruct.FinitePlaceOf K₁ K₁') (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers K₁ ⧸
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers K₂ ⧸
          (Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal) ℓ := by
  intro A ℓ hℓ
  set 𝔭 := Submission.NeukirchUchida.primeOf A.1 A.2 with h𝔭
  set B := Submission.NeukirchUchida.placeMap ϕ h A with hB
  set 𝔮 := Submission.NeukirchUchida.primeOf B.1 B.2 with h𝔮
  obtain ⟨p, hp, hF𝔭, hG𝔭⟩ := k₁ 𝔭
  obtain ⟨q, hq, hF𝔮, hG𝔮⟩ := k₂ 𝔮
  -- the characteristic of `𝓞 K₁ ⧸ 𝔭` is `p`, hence `ℓ = p`
  have hchar₁ : CharP (NumberField.RingOfIntegers K₁ ⧸ 𝔭.asIdeal) p :=
    (charP_residueField_iff 𝔭 p).mp hF𝔭.residue_char
  have hℓp : ℓ = p := CharP.eq (NumberField.RingOfIntegers K₁ ⧸ 𝔭.asIdeal) hℓ hchar₁
  -- the local theorem: `p = q`
  have hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A.1).map
      (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) = NK.Mine.decompositionGroupOf K₂ K₂' B.1 :=
    Submission.NeukirchUchida.placeMap_spec ϕ h A
  have hpq : p = q := (NK.LocalInputs.residueChar_and_localDegree_eq_of_decompositionGroup
    𝔭 𝔮 A.1 B.1 (Submission.NeukirchUchida.primeOf_spec A.1 A.2)
    (Submission.NeukirchUchida.primeOf_spec B.1 B.2) ϕ hAB hF𝔭 hG𝔭 hF𝔮 hG𝔮).1
  rw [hℓp, hpq]
  exact (charP_residueField_iff 𝔮 q).mp hF𝔮.residue_char

/-- **The absolute local degree is preserved by the place correspondence.** -/
theorem localDegree_preserved_of_localInputs
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p ∧
        NK.LocalInputs.LocalGaloisInputs K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q ∧
        NK.LocalInputs.LocalGaloisInputs K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q) :
    ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ) *
          ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ) =
        ((Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ) *
          ((Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.ramificationIdx ℤ) := by
  intro A
  set 𝔭 := Submission.NeukirchUchida.primeOf A.1 A.2 with h𝔭
  set B := Submission.NeukirchUchida.placeMap ϕ h A with hB
  set 𝔮 := Submission.NeukirchUchida.primeOf B.1 B.2 with h𝔮
  obtain ⟨p, hp, hF𝔭, hG𝔭⟩ := k₁ 𝔭
  obtain ⟨q, hq, hF𝔮, hG𝔮⟩ := k₂ 𝔮
  have hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A.1).map
      (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) = NK.Mine.decompositionGroupOf K₂ K₂' B.1 :=
    Submission.NeukirchUchida.placeMap_spec ϕ h A
  have hd : NK.LocalInputs.localDegree K₁ 𝔭 = NK.LocalInputs.localDegree K₂ 𝔮 :=
    (NK.LocalInputs.residueChar_and_localDegree_eq_of_decompositionGroup
      𝔭 𝔮 A.1 B.1 (Submission.NeukirchUchida.primeOf_spec A.1 A.2)
      (Submission.NeukirchUchida.primeOf_spec B.1 B.2) ϕ hAB hF𝔭 hG𝔭 hF𝔮 hG𝔮).2
  rw [mul_comm ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ),
      mul_comm ((Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
        (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ)]
  rw [h𝔭, h𝔮]
  rw [← NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg 𝔭]
  rw [← NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg 𝔮]
  exact hd

/-! ## The place correspondence (input (a)) from the local inputs -/

/-- **Input (a) of the endgame from the local arithmetic inputs.**

Given

* the local Brauer data at every finite prime of both fields (the local computation
  `Br(κ)[p] ≅ ℤ/p`, the Hasse principle, and Neukirch's local finishing step), which gives CoNF
  (12.1.9) "if" via `NK.Mine.preservesDecompositionGroups_of_localGalois`, and
* the local structure theory of the completions at every finite prime
  (`NK.LocalInputs.LocalFieldInputs` and `NK.LocalInputs.LocalGaloisInputs`), which gives the
  two arithmetic fields via `residueChar_preserved_of_localInputs` and
  `localDegree_preserved_of_localInputs`,

the place correspondence `NK.Reconstruct.LocalCorrespondence ϕ` (CoNF (12.1.9)) exists. -/
noncomputable def localCorrespondence_of_localData
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerHasse.LocalH2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerHasse.Sha2Vanishing p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerHasse.LocalDecompositionCriterion p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerHasse.LocalH2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerHasse.Sha2Vanishing p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerHasse.LocalDecompositionCriterion p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p ∧
        NK.LocalInputs.LocalGaloisInputs K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q ∧
        NK.LocalInputs.LocalGaloisInputs K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q) :
    NK.Reconstruct.LocalCorrespondence ϕ :=
  Submission.NeukirchUchida.localCorrespondenceOf ϕ
    (NK.Mine.preservesDecompositionGroups_of_localGalois ϕ hϕ hB₁ hB₂)
    (residueChar_preserved_of_localInputs ϕ
      (NK.Mine.preservesDecompositionGroups_of_localGalois ϕ hϕ hB₁ hB₂) k₁ k₂)
    (localDegree_preserved_of_localInputs ϕ
      (NK.Mine.preservesDecompositionGroups_of_localGalois ϕ hϕ hB₁ hB₂) k₁ k₂)

/-! ## The endgame from the local inputs -/

/-- **Neukirch–Uchida from the local inputs and the two reconstruction inputs.**  This is the
complete assembly of the existence half; its hypotheses are the genuine remaining obligations,
namely, for every finite prime of both number fields,

* the local Brauer data (`LocalH2Input`, `Sha2Vanishing`, `LocalDecompositionCriterion`) — CoNF
  (12.1.9) "if" / Neukirch's Theorem 1;
* the local structure theory of the completion (`LocalFieldInputs`, `LocalGaloisInputs`);

together with

* the local–global residue-field dictionary `NK.FrobeniusBridge.PlaceLevelBridge` at every finite
  place of both separable closures and the local structure inputs `TameDataAtPlaces` — input (b);
* the reconstruction `hd`: for the place map induced by `ϕ`, a base-field-mapping field isomorphism
  of the separable closures realizing it — input (c) of `Submission/NeukirchUchida/Endgame.lean`.

The conclusion is the existence half of CoNF XII Theorem 12.2.1. -/
theorem exists_sigma_of_localData
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerHasse.LocalH2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerHasse.Sha2Vanishing p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerHasse.LocalDecompositionCriterion p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerHasse.LocalH2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerHasse.Sha2Vanishing p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerHasse.LocalDecompositionCriterion p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) p ∧
        NK.LocalInputs.LocalGaloisInputs K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) q ∧
        NK.LocalInputs.LocalGaloisInputs K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q)
    (hD₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
      NK.FrobeniusBridge.PlaceLevelBridge A)
    (hD₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
      NK.FrobeniusBridge.PlaceLevelBridge B)
    (hTame : NK.FrobeniusBridge.TameDataAtPlaces K₂ K₂')
    (hd : ∀ h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ,
      ∃ (σ : K₂' ≃+* K₁')
        (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
        ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
          ((Submission.NeukirchUchida.placeMap ϕ h A).1).comap (σ.symm : K₁' →+* K₂') = A.1) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  -- the arithmetic of the local field (`LocalFieldInputs`) follows from the residue characteristic
  have k₁' : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p ∧
        NK.LocalInputs.LocalGaloisInputs K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p := by
    intro 𝔭
    obtain ⟨p, hp, hres, hG⟩ := k₁ 𝔭
    exact ⟨p, hp, NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔭 hp hres, hG⟩
  have k₂' : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q ∧
        NK.LocalInputs.LocalGaloisInputs K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q := by
    intro 𝔮
    obtain ⟨q, hq, hres, hG⟩ := k₂ 𝔮
    exact ⟨q, hq, NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔮 hq hres, hG⟩
  set h := NK.Mine.preservesDecompositionGroups_of_localGalois ϕ hϕ hB₁ hB₂ with hh
  set a := Submission.NeukirchUchida.localCorrespondenceOf ϕ h
    (residueChar_preserved_of_localInputs ϕ h k₁' k₂')
    (localDegree_preserved_of_localInputs ϕ h k₁' k₂') with ha
  refine NK.FrobeniusBridge.exists_sigma_of_tameData_atPlaces ϕ hϕ a hD₁ hD₂ hTame ?_
  obtain ⟨σ, hσ, hreal⟩ := hd h
  refine ⟨σ, hσ, ?_⟩
  intro A
  have h1 : (Submission.NeukirchUchida.placeMap ϕ h A) = a.placeMap A := by
    rw [ha]
    exact (NK.Reconstruct.placeEquivOf_apply ϕ h A).symm
  rw [← h1]
  exact hreal A

/-! ## The abelian rank from the *corrected* reciprocity datum

`Submission/Work/LocalCFT/` proved that the reciprocity datum
`NK.LocalReciprocity.LocalReciprocityDatum` (hence `NK.LocalReciprocity.LubinTateInput`) is
**unsatisfiable** for a `p`-adic field (see
`NK.LocalCFT.NilpotentObstruction.not_nonempty_localReciprocityDatum_of_galoisQuotient`), and
introduced the satisfiable replacement `NK.LocalCFT.ArtinReciprocity`, whose Artin map lands in
`Gal(F^{ab}/F)`.  Consequently every transfer of invariants along the sibling area's datum — in
particular `NK.LocalInputs.hasAbelianFrattiniRank_of_lubinTate`, on which the local-degree
invariance rests — is vacuous.

This lemma re-routes the transfer through the corrected datum: the abelianised `p`-Frattini rank
of `Gal(K'/κ)` equals that of the profinite completion of `κˣ`.  The two ingredients are the
infinite-level reciprocity `NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion` (through
`NK.LocalCFT.hasFrattiniRank_AbGal_of_datum`) and the passage from the topological to the abstract
abelianisation (`NK.LocalInputs.AbelianRank.hasAbelianFrattiniRank_of_maxAbelian_of_isOpen`), whose
openness hypothesis holds for `p`-adic `κ` by Nikolov–Segal. -/
theorem hasAbelianFrattiniRank_of_artinReciprocity {F F' : Type*} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F') {p r : ℕ}
    (hopen : ∀ H : Subgroup (Gal(F'/F)), H.index = p → H.Normal → IsOpen (H : Set (Gal(F'/F))))
    (h : NK.LocalAnabelian.HasFrattiniRank p r (NK.LocalReciprocity.completionUnits F)) :
    NK.LocalAnabelian.HasAbelianFrattiniRank p r (Gal(F'/F)) :=
  NK.LocalInputs.AbelianRank.hasAbelianFrattiniRank_of_maxAbelian_of_isOpen hopen
    (NK.LocalCFT.hasFrattiniRank_AbGal_of_datum D h)

end NK.Mine
