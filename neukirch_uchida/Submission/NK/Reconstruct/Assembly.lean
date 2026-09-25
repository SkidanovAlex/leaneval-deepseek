import Submission.NK.Reconstruct.Reconstruction
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.NK.NeukirchUchida.primeMap_bijective
import Submission.NK.Reconstruct.topologicalClosure_isFrobElement_eq_top
import Submission.NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Reconstruct.frobeniusCorrespondence_of_place
import Submission.NK.Reconstruct.agreesOnLevels_of_realizesPlaceMap

/-!
# Assembling the inputs of the reconstruction, and determinacy by Frobenius elements

This file contains the two pieces of *interface* that make the reconstruction theorem usable:

* `NK.Reconstruct.goodLocalCorrespondenceOf` — the input (a) `GoodLocalCorrespondence ϕ` of the
  reconstruction, assembled from the group-theoretic local correspondence
  `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` of `Reduction.lean` (CoNF (12.1.9))
  together with a realizing field isomorphism `σ` and the two arithmetic conditions on the
  corresponding primes (preservation of the residue characteristic and of the local degree, which
  the local structure theory supplies);
* `NK.Reconstruct.eq_of_eq_on_isFrobElement` — the *unconditional* group-theoretic rigidity: an
  isomorphism of absolute Galois groups of number fields which agrees with another on every
  Frobenius element is equal, because the Frobenius elements topologically generate `G_K`
  (`NK.Reconstruct.topologicalClosure_isFrobElement_eq_top`).
-/

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- The place map of `Submission.NeukirchUchida.PlaceSystem` as a bijection of the place systems. -/
noncomputable def placeEquivOf (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ) :
    FinitePlaceOf K₁ K₁' ≃ FinitePlaceOf K₂ K₂' :=
  Equiv.ofBijective (Submission.NeukirchUchida.placeMap ϕ h)
    (Submission.NeukirchUchida.placeMap_bijective ϕ h)

@[simp] lemma placeEquivOf_apply (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (A : FinitePlaceOf K₁ K₁') :
    placeEquivOf ϕ h A = Submission.NeukirchUchida.placeMap ϕ h A := rfl

/-- The induced map on primes of `Submission.NeukirchUchida.PrimeCorrespondence` as a bijection. -/
noncomputable def primeEquivOf (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ) :
    NK.Chebotarev.PrimeIdeal K₁ ≃ NK.Chebotarev.PrimeIdeal K₂ :=
  Equiv.ofBijective (Submission.NeukirchUchida.primeMap ϕ h)
    (NK.NeukirchUchida.primeMap_bijective ϕ h)

@[simp] lemma primeEquivOf_apply (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (p : NK.Chebotarev.PrimeIdeal K₁) :
    primeEquivOf ϕ h p = Submission.NeukirchUchida.primeMap ϕ h p := rfl

/-- **Assembling the good local correspondence (input (a)) from the input of
`Submission.NeukirchUchida.Reduction`.**

Given

* `h : PreservesDecompositionGroups ϕ` — the local correspondence of CoNF XII (12.1.9); it induces
  the Galois-equivariant bijection `placeMap ϕ h` of the place systems (`placeMap_bijective`,
  `placeMap_smul`, `placeMap_spec`) and the induced bijection `primeMap ϕ h` of the finite primes
  (`primeMap_bijective`, `primeOf_placeMap`);
* a field isomorphism `σ : K₂' ≃+* K₁'` mapping the embedded `K₂` onto the embedded `K₁`
  (`MapsBase`) and realizing the place map (`hreal`);
* the arithmetic conditions `residueChar` and `localDegree` on corresponding primes (these are the
  content of the local structure theory of `p`-adic fields, CoNF XII §12.1, and are *not* proved
  here),

one obtains the input (a) of `NK.Reconstruct.exists_sigma_of_goodLocalCorrespondence`. -/
noncomputable def goodLocalCorrespondenceOf (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hreal : ∀ A : Submission.NeukirchUchida.FinitePlace K₁ K₁',
      (Submission.NeukirchUchida.placeMap ϕ h A).1.comap (σ.symm : K₁' →+* K₂') = A.1)
    (residueChar : ∀ (p : NK.Chebotarev.PrimeIdeal K₁) (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers K₁ ⧸ p.asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers K₂ ⧸
          (Submission.NeukirchUchida.primeMap ϕ h p).asIdeal) ℓ)
    (localDegree : ∀ p : NK.Chebotarev.PrimeIdeal K₁,
      p.asIdeal.inertiaDeg ℤ * p.asIdeal.ramificationIdx ℤ =
        (Submission.NeukirchUchida.primeMap ϕ h p).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeMap ϕ h p).asIdeal.ramificationIdx ℤ) :
    GoodLocalCorrespondence ϕ where
  placeMap := placeEquivOf ϕ h
  map_smul := fun g A => by
    rw [placeEquivOf_apply, placeEquivOf_apply]
    exact Subtype.ext (congrArg Subtype.val (Submission.NeukirchUchida.placeMap_smul ϕ h g A))
  map_decomp := fun A => by
    rw [placeEquivOf_apply]
    exact Submission.NeukirchUchida.placeMap_spec ϕ h A
  primeMap := primeEquivOf ϕ h
  primeMap_spec := fun A => by
    rw [primeEquivOf_apply, placeEquivOf_apply]
    exact (Submission.NeukirchUchida.primeOf_placeMap h A).symm
  residueChar := fun A ℓ hℓ => by
    rw [placeEquivOf_apply, Submission.NeukirchUchida.primeOf_placeMap h A]
    exact residueChar _ ℓ hℓ
  localDegree := fun A => by
    rw [placeEquivOf_apply, Submission.NeukirchUchida.primeOf_placeMap h A]
    exact localDegree _
  sigma := σ
  sigma_mapsBase := hσ
  sigma_realizes := fun A => hreal A
/-- **The reconstruction theorem from the inputs of `Submission.NeukirchUchida.Reduction`.**

This is the form of the core theorem to use when the local correspondence is available in the shape
of the existing workspace development:

* `h : PreservesDecompositionGroups ϕ` — CoNF (12.1.9);
* `σ` realizing the induced place map in the sense of `RealizesPlaceMap ϕ σ hσ` (input (B) of
  `Reduction.lean`); converted into the place form by
  `comap_placeMap_eq_of_realizesPlaceMap`;
* the two arithmetic conditions `residueChar` and `localDegree` of the local structure theory;
* the Frobenius correspondence (b) and the Čebotarev input (c).

In particular **no local rigidity input is used**: the endgame runs on (b) + (c) alone. -/
theorem exists_sigma_of_localCorrespondence_of_reduction (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hsub : Submission.NeukirchUchida.RealizesPlaceMap ϕ σ hσ)
    (residueChar : ∀ (p : NK.Chebotarev.PrimeIdeal K₁) (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers K₁ ⧸ p.asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers K₂ ⧸
          (Submission.NeukirchUchida.primeMap ϕ h p).asIdeal) ℓ)
    (localDegree : ∀ p : NK.Chebotarev.PrimeIdeal K₁,
      p.asIdeal.inertiaDeg ℤ * p.asIdeal.ramificationIdx ℤ =
        (Submission.NeukirchUchida.primeMap ϕ h p).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeMap ϕ h p).asIdeal.ramificationIdx ℤ)
    (b : FrobeniusCorrespondence ϕ σ) (c : ChebotarevInput K₁ K₁') :
    ∃ σ' : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ' ϕ :=
  exists_sigma_of_goodLocalCorrespondence ϕ
    (goodLocalCorrespondenceOf ϕ h σ hσ
      (comap_placeMap_eq_of_realizesPlaceMap h σ hσ hsub) residueChar localDegree) b c

/-- **The reconstruction with σ-free hypotheses** (the form of the deliverable).

The hypotheses are exactly the three named inputs in σ-free form:

* `a : LocalCorrespondence ϕ` — the good local correspondence of CoNF (12.1.9) (input (a));
* `b : FrobeniusCorrespondencePlace ϕ hϕ a` — the σ-free Frobenius correspondence (input (b)):
  `ϕ` matches the Frobenius elements at corresponding places (those corresponding under
  `a.placeMap`) and corresponding levels (`levelMap ϕ`);
* `c : ChebotarevInput K₁ K₁'` — the Čebotarev density input (input (c)):

together with the *single* remaining ingredient: the existence of a field isomorphism `σ : K₂' ≃+* K₁'`
mapping the embedded `K₂` onto the embedded `K₁` and realizing the place correspondence (this is the
output of Neukirch CoNF XII §12.2, resp. of Shimizu's §4, and is the one genuinely deep input).  The conclusion is that this `σ` reconstructs `ϕ`:
`ϕ g = σ⁻¹ g σ` for all `g`.

The witness `σ` is supplied by (d) (the deep reconstruction input of CoNF XII §12.2), and the
Frobenius correspondence (b) is transferred to `σ` by
`NK.Reconstruct.frobeniusCorrespondence_of_place`.  Nothing else is used. -/
theorem exists_sigma_of_localCorrespondence_sigmaFree (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ) (b : FrobeniusCorrespondencePlace ϕ hϕ a)
    (c : ChebotarevInput K₁ K₁')
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : FinitePlaceOf K₁ K₁', (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, hreal⟩ := d
  exact exists_sigma_of_frobeniusCorrespondence ϕ σ hσ
    (frobeniusCorrespondence_of_place hϕ a σ hσ hreal
      (agreesOnLevels_of_realizesPlaceMap hϕ a σ hσ hreal) b) c

/-- **Determinacy by Frobenius elements.**  Two continuous homomorphisms out of `Gal(K'/K)`,
`K` a number field, which agree on every Frobenius element are equal: the Frobenius elements
topologically generate `Gal(K'/K)`
(`NK.Reconstruct.topologicalClosure_isFrobElement_eq_top`). -/
theorem eq_of_eq_on_isFrobElement {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {H : Type*} [Group H] [TopologicalSpace H] [T2Space H]
    (φ ψ : Gal(K'/K) →* H) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ g : Gal(K'/K), IsFrobElement g → φ g = ψ g) : φ = ψ := by
  let E : Subgroup Gal(K'/K) :=
    { carrier := {g | φ g = ψ g}
      one_mem' := by show φ 1 = ψ 1; rw [map_one, map_one]
      mul_mem' := by
        intro a b ha hb
        show φ (a * b) = ψ (a * b)
        rw [map_mul, map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        show φ a⁻¹ = ψ a⁻¹
        rw [map_inv, map_inv, ha] }
  have hEclosed : IsClosed (E : Set Gal(K'/K)) := isClosed_eq hφ hψ
  have hle : Subgroup.closure {g : Gal(K'/K) | IsFrobElement g} ≤ E :=
    (Subgroup.closure_le E).mpr fun g hg => h g hg
  have htop : E = ⊤ := by
    have h1 : (Subgroup.closure {g : Gal(K'/K) | IsFrobElement g}).topologicalClosure ≤ E :=
      Subgroup.topologicalClosure_minimal _ hle hEclosed
    rw [topologicalClosure_isFrobElement_eq_top] at h1
    exact top_le_iff.mp h1
  exact MonoidHom.ext fun g => by
    have : g ∈ E := by rw [htop]; trivial
    exact this

end NK.Reconstruct
