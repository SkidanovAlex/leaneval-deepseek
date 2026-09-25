import Submission.NK.FrobeniusBridge.Main

/-!
# The Frobenius bridge: the place-level correspondence from the local theory

This file derives the place-level Frobenius correspondence for `ϕ`
(`NK.FrobeniusBridge.LocalFrobCorrespondencePlace`, the hypothesis `hB` of the deliverable) from
the local structure theory of the two fields, i.e. from `NK.LocalTame.TameData` and
`NK.LocalTame.Zl2ResidueChar` at the corresponding places — precisely the output of
`Submission/Work/LocalTame/`, in particular of its global corollary
`NK.LocalTame.frobenius_matching_at_corresponding_places` (Shimizu, arXiv:2009.10431, Lemma 2.1;
NSW (12.1.8) Lemma).

Two forms are provided:

* `localFrobCorrespondencePlace_of_localTame`: from the matching of the Frobenius lifts at the two
  places, in the exact vocabulary of `NK.LocalTame.IsFrobeniusLiftOfDecomposition`
  (this is the shape requested by the endgame);
* `localFrobCorrespondencePlace_of_tameData`: from the local structure inputs alone, applying
  `NK.LocalTame.frobenius_matching_at_corresponding_places` (the form with no unproved
  hypothesis beyond the named local inputs).
-/

namespace NK.FrobeniusBridge

open scoped Classical Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

variable {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
  (a : NK.Reconstruct.LocalCorrespondence ϕ)

/-- **The local structure inputs at every place of `K'`**: for the completion of `K` at the prime
below each place of `K'` there are `p`, `q` with `NK.LocalTame.TameData` and
`NK.LocalTame.Zl2ResidueChar`.  This is the output of the local structure theory
(`Submission/Work/LocalStructure/`, `Submission/Work/LocalInputs/`) for a number field. -/
def TameDataAtPlaces (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K'] [Algebra K K']
    [IsSepClosure K K'] : Prop :=
  ∀ A : FinitePlaceOf K K', ∃ p q : ℕ,
    NK.LocalTame.TameData p q (localField A) (localClosure A) ∧
    NK.LocalTame.Zl2ResidueChar p (localField A) (localClosure A)

/-- The local structure inputs (`NK.LocalTame.TameData` and
`NK.LocalTame.Zl2ResidueChar`) for the completion of `K₂` at the prime below the place
`a.placeMap A` corresponding to a place `A` of `K₁'`. -/
def TameDataAtImage (a : NK.Reconstruct.LocalCorrespondence ϕ) : Prop :=
  ∀ A : FinitePlaceOf K₁ K₁', ∃ p q : ℕ,
    NK.LocalTame.TameData p q (localField (a.placeMap A)) (localClosure (a.placeMap A)) ∧
    NK.LocalTame.Zl2ResidueChar p (localField (a.placeMap A)) (localClosure (a.placeMap A))

/-- The local structure inputs at the image places follow from those at every place of `K₂'`. -/
theorem TameDataAtImage.of_atPlaces (h : TameDataAtPlaces K₂ K₂') : TameDataAtImage a :=
  fun A => h (a.placeMap A)

/-- **The place-level Frobenius correspondence from the matching of the Frobenius lifts at the two
places** — the form in which `NK.LocalTame.frobenius_matching_at_corresponding_places` delivers
it.  The hypothesis `hLoc` is exactly the conclusion of
`NK.LocalTame.frobenius_matching_at_corresponding_places_chosen`; the hypothesis `hTame` supplies
the local structure inputs at the image places, which `hLoc` takes as arguments. -/
theorem localFrobCorrespondencePlace_of_localTame (hTame : TameDataAtImage a)
    (hLoc : ∀ (A : FinitePlaceOf K₁ K₁') (p₁ q₁ p₂ q₂ : ℕ)
      (hT₁ : NK.LocalTame.TameData p₁ q₁ (localField A) (localClosure A))
      (hT₂ : NK.LocalTame.TameData p₂ q₂ (localField (a.placeMap A))
        (localClosure (a.placeMap A)))
      (hZ₁ : NK.LocalTame.Zl2ResidueChar p₁ (localField A) (localClosure A))
      (hZ₂ : NK.LocalTame.Zl2ResidueChar p₂ (localField (a.placeMap A))
        (localClosure (a.placeMap A)))
      (τ : Gal(K₁'/K₁))
      (hτ : τ ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A.1),
      NK.LocalTame.IsFrobeniusLiftOfDecomposition p₁ q₁ (localGaloisEquiv A) ⟨τ, hτ⟩ →
      NK.LocalTame.IsFrobeniusLiftOfDecomposition p₂ q₂ (localGaloisEquiv (a.placeMap A))
        (NK.LocalTame.mulEquivSubgroupCongr ϕ (a.map_decomp A) ⟨τ, hτ⟩)) :
    LocalFrobCorrespondencePlace ϕ hϕ a := by
  intro A g hg
  obtain ⟨hgD, p₁, q₁, hT₁, hZ₁, hF₁⟩ := hg
  obtain ⟨p₂, q₂, hT₂, hZ₂⟩ := hTame A
  refine ⟨?_, p₂, q₂, hT₂, hZ₂, hLoc A p₁ q₁ p₂ q₂ hT₁ hT₂ hZ₁ hZ₂ g hgD hF₁⟩
  rw [← a.map_decomp A]
  exact Subgroup.mem_map.mpr ⟨g, hgD, rfl⟩

/-- **The place-level Frobenius correspondence from the local structure theory**: the matching of
the Frobenius lifts at corresponding places for an isomorphism `ϕ` of absolute Galois groups is
`NK.LocalTame.frobenius_matching_at_corresponding_places` (Shimizu Lemma 2.1 / CoNF (12.1.8)) —
this file only converts its conclusion into the predicate `LocalFrobCorrespondencePlace` of the
Frobenius bridge. -/
theorem localFrobCorrespondencePlace_of_tameData (hTame : TameDataAtImage a) :
    LocalFrobCorrespondencePlace ϕ hϕ a :=
  localFrobCorrespondencePlace_of_localTame (ϕ := ϕ) hϕ a hTame
    (fun A p₁ q₁ p₂ q₂ hT₁ hT₂ hZ₁ hZ₂ τ hτ hF =>
      NK.LocalTame.frobenius_matching_at_corresponding_places
        (Submission.NeukirchUchida.primeOf A.1 A.2)
        (Submission.NeukirchUchida.primeOf (a.placeMap A).1 (a.placeMap A).2)
        A.1 (Submission.NeukirchUchida.primeOf_spec A.1 A.2)
        (a.placeMap A).1
        (Submission.NeukirchUchida.primeOf_spec (a.placeMap A).1 (a.placeMap A).2)
        ϕ (a.map_decomp A) hT₁ hT₂ hZ₁ hZ₂ (localGaloisEquiv A)
        (localGaloisEquiv (a.placeMap A)) ⟨τ, hτ⟩ |>.mp hF)


/-- **The Frobenius bridge, assembled from the local structure theory**: the finite-level,
σ-free Frobenius correspondence `NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a` — input (b)
of the Neukirch–Uchida endgame — follows from

* the local–global dictionary `NK.FrobeniusBridge.PlaceLevelBridge` at every place of the two
  fields (the named arithmetic input, see `Bridge.lean`), and
* the local structure theory `NK.LocalTame.TameData`/`NK.LocalTame.Zl2ResidueChar` at the
  places of `K₂'` corresponding to the places of `K₁'`,

with no further hypothesis: the place-level Frobenius correspondence for `ϕ` is
`NK.LocalTame.frobenius_matching_at_corresponding_places` (Shimizu Lemma 2.1). -/
theorem frobeniusCorrespondencePlace_of_tameData (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hD₁ : ∀ A : FinitePlaceOf K₁ K₁', PlaceLevelBridge A)
    (hD₂ : ∀ B : FinitePlaceOf K₂ K₂', PlaceLevelBridge B)
    (hTame : TameDataAtImage a) :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a :=
  frobeniusCorrespondencePlace_of_bridge ϕ hϕ a hD₁ hD₂
    (localFrobCorrespondencePlace_of_tameData (ϕ := ϕ) hϕ a hTame)

/-- **The requested name for the second deliverable**: the place-level Frobenius correspondence
(`hB`) from the matching of the Frobenius lifts at the two places, in the vocabulary of
`NK.LocalTame.IsFrobeniusLiftOfDecomposition`
(this is `localFrobCorrespondencePlace_of_localTame`; the hypothesis `hTame` supplies the local
structure inputs at the image places, which `hLoc` takes as arguments). -/
theorem placeFrobeniusCorrespondence_of_localTame (hTame : TameDataAtImage a)
    (hLoc : ∀ (A : FinitePlaceOf K₁ K₁') (p₁ q₁ p₂ q₂ : ℕ)
      (hT₁ : NK.LocalTame.TameData p₁ q₁ (localField A) (localClosure A))
      (hT₂ : NK.LocalTame.TameData p₂ q₂ (localField (a.placeMap A))
        (localClosure (a.placeMap A)))
      (hZ₁ : NK.LocalTame.Zl2ResidueChar p₁ (localField A) (localClosure A))
      (hZ₂ : NK.LocalTame.Zl2ResidueChar p₂ (localField (a.placeMap A))
        (localClosure (a.placeMap A)))
      (τ : Gal(K₁'/K₁))
      (hτ : τ ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A.1),
      NK.LocalTame.IsFrobeniusLiftOfDecomposition p₁ q₁ (localGaloisEquiv A) ⟨τ, hτ⟩ →
      NK.LocalTame.IsFrobeniusLiftOfDecomposition p₂ q₂ (localGaloisEquiv (a.placeMap A))
        (NK.LocalTame.mulEquivSubgroupCongr ϕ (a.map_decomp A) ⟨τ, hτ⟩)) :
    LocalFrobCorrespondencePlace ϕ hϕ a :=
  localFrobCorrespondencePlace_of_localTame hϕ a hTame hLoc

/-- **The place-level Frobenius correspondence from the local structure theory at every place of
`K₂'`** (the natural form of the hypothesis). -/
theorem localFrobCorrespondencePlace_of_tameData_atPlaces (h : TameDataAtPlaces K₂ K₂') :
    LocalFrobCorrespondencePlace ϕ hϕ a :=
  localFrobCorrespondencePlace_of_tameData hϕ a (TameDataAtImage.of_atPlaces a h)

/-- **The finite-level, σ-free Frobenius correspondence from the local structure theory at every
place of `K₂'` and the local–global dictionary at the places of both fields.** -/
theorem frobeniusCorrespondencePlace_of_tameData_atPlaces (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hD₁ : ∀ A : FinitePlaceOf K₁ K₁', PlaceLevelBridge A)
    (hD₂ : ∀ B : FinitePlaceOf K₂ K₂', PlaceLevelBridge B)
    (hTame : TameDataAtPlaces K₂ K₂') :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a :=
  frobeniusCorrespondencePlace_of_tameData ϕ hϕ a hD₁ hD₂ (TameDataAtImage.of_atPlaces a hTame)

end NK.FrobeniusBridge
