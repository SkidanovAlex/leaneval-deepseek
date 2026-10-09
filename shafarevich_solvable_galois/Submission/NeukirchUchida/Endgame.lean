import Submission.NK.Mine.exists_sigma_of_frobeniusCorrespondence
import Submission.NK.Reconstruct.Assembly
import Submission.NK.Reconstruct.agreesOnLevels_of_map_decompositionGroup
import Submission.NK.Reconstruct.frobeniusCorrespondence_of_place
import Submission.NK.ReconstructField.Main
import Submission.NeukirchUchida.Reduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The endgame of Neukirch–Uchida: assembling `exists_sigma`

Reference: Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, XII §12.1–§12.2.

This file performs the *final assembly* of the existence half of the theorem from the three named
inputs of the development:

* **(a) the place correspondence** `a : NK.Reconstruct.LocalCorrespondence ϕ` — CoNF (12.1.9),
  i.e. `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` (produced by
  `Submission/Work/BrauerHasse/` together with the local structure theory) plus the arithmetic
  content (preservation of the residue characteristic and of the local degree `[κ : ℚ_p]`,
  produced by `Submission/Work/LocalInputs/`).  The construction of `a` from
  `PreservesDecompositionGroups ϕ` and the arithmetic data is `NK.Reconstruct.placeEquivOf`,
  `NK.Reconstruct.primeEquivOf` and `NK.Reconstruct.goodLocalCorrespondenceOf`;
* **(b) the local Frobenius correspondence** `b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a`
  — the statement that `ϕ` matches the Frobenius elements at corresponding places (delivered by
  `Submission/Work/LocalTame/` from the local structure theory);
* **(c) the reconstruction** `d` — a field isomorphism `σ : K₂' ≃+* K₁'` mapping the embedded `K₂`
  onto the embedded `K₁` (i.e. `MapsBase`) and realizing the place correspondence, in the form
  `(a.placeMap A).1.comap σ.symm = A.1` for every finite place `A`.  This is the deep input of
  CoNF XII §12.2 (Neukirch's Invent. Math. 6 (1969) argument, resp. Shimizu,
  arXiv:2009.10431 §4); producing it is the deliverable of `Submission/Work/ReconstructField/`.

Given (a) and (c), the level correspondence of `σ` agrees with that of `ϕ`
(`NK.Reconstruct.agreesOnLevels_of_map_decompositionGroup`, which uses the fact that the
completely split primes determine a finite normal subextension,
`NK.Reconstruct.eq_of_splitPrimes_eq` — an unconditional density argument).  With (b) this gives
the σ-based Frobenius correspondence (`NK.Reconstruct.frobeniusCorrespondence_of_place`), and
`NK.Mine.exists_sigma_of_frobeniusCorrespondence` concludes `Conjugates σ ϕ`.

In particular **no Čebotarev density input, no homeomorphism hypothesis beyond `IsHomeomorph ϕ`, and
no local rigidity input are used**: the whole remaining mathematical obligation is (c).
-/

namespace Submission.NeukirchUchida

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The place correspondence (input (a)) of CoNF (12.1.9) from its group-theoretic form.**

Given `h : PreservesDecompositionGroups ϕ` — the "if" direction of CoNF (12.1.9), produced by
`Submission/Work/BrauerHasse/` from the local Brauer group, the Hasse principle and Neukirch's local
argument — and the two arithmetic conditions on corresponding primes (preservation of the residue
characteristic and of the local degree `[κ : ℚ_p]`, produced by `Submission/Work/LocalInputs/`),
this is the σ-free input (a) of the reconstruction, in the shape
`NK.Reconstruct.LocalCorrespondence ϕ`. -/
noncomputable def localCorrespondenceOf (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : PreservesDecompositionGroups ϕ)
    (residueChar : ∀ (A : NK.Reconstruct.FinitePlaceOf K₁ K₁') (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers K₁ ⧸ (primeOf A.1 A.2).asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers K₂ ⧸
          (primeOf (placeMap ϕ h A).1 (placeMap ϕ h A).2).asIdeal) ℓ)
    (localDegree : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      (primeOf A.1 A.2).asIdeal.inertiaDeg ℤ * (primeOf A.1 A.2).asIdeal.ramificationIdx ℤ =
        (primeOf (placeMap ϕ h A).1 (placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ *
          (primeOf (placeMap ϕ h A).1 (placeMap ϕ h A).2).asIdeal.ramificationIdx ℤ) :
    NK.Reconstruct.LocalCorrespondence ϕ where
  placeMap := NK.Reconstruct.placeEquivOf ϕ h
  map_smul := fun g A => by
    rw [NK.Reconstruct.placeEquivOf_apply, NK.Reconstruct.placeEquivOf_apply]
    exact placeMap_smul ϕ h g A
  map_decomp := fun A => placeMap_spec ϕ h A
  primeMap := NK.Reconstruct.primeEquivOf ϕ h
  primeMap_spec := fun A => by
    rw [NK.Reconstruct.primeEquivOf_apply, NK.Reconstruct.placeEquivOf_apply]
    exact (primeOf_placeMap h A).symm
  residueChar := residueChar
  localDegree := localDegree

/-- **The realization of the place map transported to the decomposition groups.**

If `σ : K₂' ≃+* K₁'` is `MapsBase` and realizes the place correspondence `a` of `ϕ`, i.e.
`(a.placeMap A).1 = A.comap σ` for every finite place `A` of `K₁'`, then the conjugation by `σ`
and `ϕ` agree on every decomposition group.  This is the hypothesis `hpres` of
`NK.Reconstruct.agreesOnLevels_of_map_decompositionGroup`. -/
theorem map_decompositionGroup_eq_of_comap_placeMap_eq
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (a : NK.Reconstruct.LocalCorrespondence ϕ)
    {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hreal : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1)
    (A : ValuationSubring K₁') (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) :
    ((decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))).map
      ((conjHomEquiv hσ).symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)) =
      decompositionGroup (K₁ := K₁) (K₁' := K₁') A := by
  -- the transported place is `A.comap σ`
  have hB : (a.placeMap ⟨A, hA⟩).1 = A.comap (σ : K₂' →+* K₁') := by
    have h1 : ∀ x : K₁', σ.symm x ∈ (a.placeMap ⟨A, hA⟩).1 ↔ x ∈ A.1 := by
      intro x
      have hmem : x ∈ (a.placeMap ⟨A, hA⟩).1.comap (σ.symm : K₁' →+* K₂') ↔
          σ.symm x ∈ (a.placeMap ⟨A, hA⟩).1 := ValuationSubring.mem_comap
      rw [hreal ⟨A, hA⟩] at hmem
      exact hmem.symm
    ext y
    rw [ValuationSubring.mem_comap]
    simpa using h1 (σ y)
  -- hence `ϕ(D_A) = D_{A.comap σ}` and the conjugation by `σ` inverts this
  have hmap : (decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
      (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) = decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (A.comap (σ : K₂' →+* K₁')) := by
    rw [a.map_decomp ⟨A, hA⟩, hB]
  rw [hmap, ← NK.Reconstruct.map_conjHomEquiv_decompositionGroup hσ A]
  exact NK.Reconstruct.subgroup_map_map_symm (conjHomEquiv hσ)
    (decompositionGroup (K₁ := K₁) (K₁' := K₁') A)

/-- **The endgame.**  The three named inputs (a), (b), (c) of the module docstring yield the
existence half of Neukirch–Uchida. -/
theorem exists_sigma_of_reconstruction
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a)
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    ∃ σ : K₂' ≃+* K₁', Conjugates σ ϕ := by
  obtain ⟨σ, hσ, hreal⟩ := d
  refine NK.Mine.exists_sigma_of_frobeniusCorrespondence ϕ σ hσ ?_
  exact NK.Reconstruct.frobeniusCorrespondence_of_place hϕ a σ hσ hreal
    (NK.Reconstruct.agreesOnLevels_of_map_decompositionGroup hϕ σ hσ
      (fun A hA => map_decompositionGroup_eq_of_comap_placeMap_eq a hσ hreal A hA)) b

/-- **The endgame, with the σ-based Frobenius correspondence bundled**: it suffices to produce
`σ` with `MapsBase` together with the Frobenius correspondence relative to `σ`. -/
theorem exists_sigma_of_frobeniusCorrespondence
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      NK.Reconstruct.FrobeniusCorrespondence ϕ σ) :
    ∃ σ : K₂' ≃+* K₁', Conjugates σ ϕ := by
  obtain ⟨σ, hσ, hb⟩ := d
  exact NK.Mine.exists_sigma_of_frobeniusCorrespondence ϕ σ hσ hb

/-- **The endgame from the reconstruction input of `Submission/Work/ReconstructField/`.**

`NK.ReconstructField.ReconstructionInput hϕ a` is the sharpest known form of the remaining
obligation: there are a base-field isomorphism `τ : K₁ ≃+* K₂` and a Galois twist `h ∈ Gal(K₂'/K₂)`
such that the corresponding `MapsBase` isomorphism of the separable closures realizes the place
correspondence `a` (Neukirch, Invent. Math. 6 (1969), Satz 2; CoNF XII §12.2; Shimizu,
arXiv:2009.10431, Theorems 4.0–4.3).  With the place correspondence (a) and the local Frobenius
correspondence (b) this yields the existence half — **with no Čebotarev input and no local
rigidity input**. -/
theorem exists_sigma_of_reconstructionInput
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a)
    (hC : NK.ReconstructField.ReconstructionInput hϕ a) :
    ∃ σ : K₂' ≃+* K₁', Conjugates σ ϕ := by
  obtain ⟨σ, hσ, hfrob⟩ :=
    NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius ϕ hϕ a b hC
  exact NK.Mine.exists_sigma_of_frobeniusCorrespondence ϕ σ hσ hfrob

end Submission.NeukirchUchida
