import Mathlib
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.ReconstructField.LevelPrime
import Submission.NK.ReconstructField.LevelPrimeBijective
import Submission.NK.ReconstructField.primeOfLevel_placeMap_eq_of_comap_eq_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The number of primes above corresponding primes at corresponding finite levels

This file proves `NK.ReconstructField.ncard_primesOver_levelPrimeMapGen`: for a finite level
`L ⊆ L'` of `K₁/K₁'` (with `L` normal over `K₁`) and the corresponding levels
`levelMap ϕ L ⊆ levelMap ϕ L'` of `K₂/K₂'`, the number of primes of `𝓞 L'` above a prime `𝔭` of
`𝓞 L` equals the number of primes of `𝓞 (levelMap ϕ L')` above the corresponding prime
`levelPrimeMap ϕ hϕ a L 𝔭`.

The statement is the general (non-normal) form of the finite-level counting statement of CoNF XII
§12.2.  The proof below does not use orbit counting abstractly, but exhibits an explicit bijection
between the two sets of primes, built from the place correspondence `a`:

* the *bridge* lemmas `liesOver_of_comap_valRing_eq` (place data for a tower of number fields
  determines `LiesOver`, proved through `Valuation.IsEquiv` of the two places) and
  `comap_eq_valRing_of_liesOver` (the converse, from `LiesOver` to the comap of the valuation
  rings);
* the well-definedness `NK.ReconstructField.primeOfLevel_placeMap_eq_of_comap_eq_gen` of the level
  prime of the image place and the (general, non-normal) injectivity
  `comap_eq_of_primeOfLevel_placeMap_eq_gen` of that map, which is proved here;
* the identification of the induced prime of the *larger* level with the given one, through the
  Galois-equivariance of `a` and the transitivity of the Galois action on the places above a fixed
  place (`Commons.FieldTheory.Galois.exists_restrictScalars_smul_eq_of_comap_eq`).

The statement refers to `NK.Reconstruct.levelMap_mono`, which is
`NK.ReconstructField.levelMap_mono`; that name is provided below before the statement.
-/


namespace NK.Reconstruct

open scoped Pointwise

/-- **The image of a level under `ϕ` is monotone**, under the name used by the statement of
`NK.ReconstructField.ncard_primesOver_levelPrimeMapGen` (which refers to it as
`NK.Reconstruct.levelMap_mono`); it is `NK.ReconstructField.levelMap_mono`. -/
theorem levelMap_mono {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) {L L' : IntermediateField K₁ K₁'} (h : L ≤ L') :
    levelMap ϕ L ≤ levelMap ϕ L' := by
  intro x hx
  rw [mem_levelMap_iff] at hx ⊢
  intro g hg
  exact hx g (fun y => hg ⟨y.1, h y.2⟩)

end NK.Reconstruct

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "valR[" K ", " v "]" => IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v

/-! ## Places above a prime of a finite level -/

/-- **A place of `K'` above a prime of a finite level**: a place of `K'` whose trace on the level
`L` is the valuation ring of `P` (`NK.ReconstructField.exists_finitePlace_of_prime_level`). -/
noncomputable def placeOverPrime {k K' : Type*} [Field k] [NumberField k] [Field K']
    [Algebra k K'] [IsSepClosure k K'] (L : IntermediateField k K') [NumberField ↥L]
    (P : NK.Chebotarev.PrimeIdeal ↥L) : NK.Reconstruct.FinitePlaceOf k K' :=
  (exists_finitePlace_of_prime_level L P).choose

/-- The defining property of `placeOverPrime`. -/
theorem placeOverPrime_spec {k K' : Type*} [Field k] [NumberField k] [Field K']
    [Algebra k K'] [IsSepClosure k K'] (L : IntermediateField k K') [NumberField ↥L]
    (P : NK.Chebotarev.PrimeIdeal ↥L) :
    (placeOverPrime L P).1.comap (algebraMap ↥L K') = valR[↥L, P] :=
  (exists_finitePlace_of_prime_level L P).choose_spec

/-- The prime of the level cut out by a chosen place above it is the prime we started with. -/
theorem primeOfLevel_placeOverPrime {k K' : Type*} [Field k] [NumberField k] [Field K']
    [Algebra k K'] [IsSepClosure k K'] (L : IntermediateField k K') [FiniteDimensional k L]
    [NumberField ↥L] (P : NK.Chebotarev.PrimeIdeal ↥L) :
    primeOfLevel (placeOverPrime L P).1 L (comap_level_ne_top (placeOverPrime L P).2 L) = P :=
  Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥L)
    ((primeOfLevel_spec (placeOverPrime L P).1 L _).symm.trans (placeOverPrime_spec L P))

/-- `primeOfLevel` only depends on the place. -/
theorem primeOfLevel_place_congr {k K' : Type*} [Field k] [NumberField k] [Field K']
    [Algebra k K'] [IsSepClosure k K'] {L : IntermediateField k K'} [NumberField ↥L]
    {A A' : NK.Reconstruct.FinitePlaceOf k K'} (h : A = A') :
    primeOfLevel A.1 L (comap_level_ne_top A.2 L) =
      primeOfLevel A'.1 L (comap_level_ne_top A'.2 L) := by
  apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥L)
  refine (primeOfLevel_spec A.1 L _).symm.trans ?_
  rw [show A.1 = A'.1 from congrArg Subtype.val h]
  exact primeOfLevel_spec A'.1 L _

/-- The scalar-tower structure on the fields induced by an inclusion hypothesis on the algebra
structure of two intermediate levels. -/
theorem isScalarTower_of_inclusion (k : Type*) [Field k] (K' : Type*) [Field K'] [Algebra k K']
    (L : IntermediateField k K') (L' : IntermediateField k K') (hLL' : L ≤ L')
    [Algebra ↥L ↥L']
    (hincl : ∀ x : ↥L, algebraMap ↥L ↥L' x = (⟨(x : K'), hLL' x.2⟩ : ↥L')) :
    IsScalarTower ↥L ↥L' K' := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext x
  simp only [RingHom.comp_apply]
  rw [IntermediateField.algebraMap_apply, hincl]
  rfl

/-! ## The bridge between primes of the rings of integers and places of the fields -/

/-- **The comap of the valuation rings determines `LiesOver`.**

If the trace on `L` of the valuation ring of the place `q` is the valuation ring of the place `p`,
then `q` lies over `p`.  The proof shows that the two valuations `q.valuation` (restricted to `K`)
and `p.valuation` are equivalent — they have the same unit ball — and then compares `1`-adic
membership in the two rings of integers. -/
theorem liesOver_of_comap_valRing_eq {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (p : NK.Chebotarev.PrimeIdeal K) (q : NK.Chebotarev.PrimeIdeal L)
    (h : (valR[L, q]).comap (algebraMap K L) = valR[K, p]) :
    q.asIdeal.LiesOver p.asIdeal := by
  have hequiv : (IsDedekindDomain.HeightOneSpectrum.valuation K p).IsEquiv
      (Valuation.comap (algebraMap K L) (IsDedekindDomain.HeightOneSpectrum.valuation L q)) := by
    apply Valuation.isEquiv_of_val_le_one
    intro x
    rw [Valuation.comap_apply, ← Valuation.mem_valuationSubring_iff,
      ← Valuation.mem_valuationSubring_iff]
    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := K) p,
      ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := L) q,
      ← h]
    rfl
  have hlt : ∀ {x : K}, (IsDedekindDomain.HeightOneSpectrum.valuation K p) x < 1 ↔
      (Valuation.comap (algebraMap K L) (IsDedekindDomain.HeightOneSpectrum.valuation L q)) x < 1 :=
    (Valuation.isEquiv_iff_val_lt_one).mp hequiv
  refine ⟨?z⟩
  ext r
  rw [Ideal.under_def, Ideal.mem_comap]
  by_cases hr : r = 0
  · subst hr; simp
  · rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) p r,
      ← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) q
        (algebraMap _ _ r)]
    refine (hlt (x := (r : K))).trans ?_
    rw [Valuation.comap_apply]
    exact iff_of_eq (congrArg (fun t : L => (IsDedekindDomain.HeightOneSpectrum.valuation L q) t < 1)
      (NumberField.RingOfIntegers.mapRingHom_apply (algebraMap K L) r).symm)

/-- **The place form of the bridge**: if a place of an overfield `K'` restricts to the valuation
rings of `p` resp. `q` on the two fields of a tower `K ⊆ L ⊆ K'`, then `q` lies over `p`. -/
theorem liesOver_of_comap_eq_valRing {K L K' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field K'] [Algebra K L] [FiniteDimensional K L] [Algebra K K']
    [Algebra L K'] [IsScalarTower K L K']
    (p : NK.Chebotarev.PrimeIdeal K) (q : NK.Chebotarev.PrimeIdeal L) (A : ValuationSubring K')
    (hq : A.comap (algebraMap L K') = valR[L, q])
    (hp : A.comap (algebraMap K K') = valR[K, p]) :
    q.asIdeal.LiesOver p.asIdeal := by
  apply liesOver_of_comap_valRing_eq p q
  rw [← hq, ValuationSubring.comap_comap A (algebraMap L K') (algebraMap K L),
    ← IsScalarTower.algebraMap_eq K L K', hp]

/-- **The converse bridge**: `LiesOver` computes the trace of the corresponding valuation rings. -/
theorem comap_eq_valRing_of_liesOver {K L K' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [Field K'] [Algebra K K']
    [Algebra L K'] [IsScalarTower K L K']
    (p : NK.Chebotarev.PrimeIdeal K) (q : NK.Chebotarev.PrimeIdeal L) (A : ValuationSubring K')
    (hq : A.comap (algebraMap L K') = valR[L, q]) (h : q.asIdeal.LiesOver p.asIdeal) :
    A.comap (algebraMap K K') = valR[K, p] := by
  rw [IsScalarTower.algebraMap_eq K L K', ← ValuationSubring.comap_comap A (algebraMap L K')
    (algebraMap K L), hq, Commons.RingTheory.Valuation.comap_valuationSubringAtPrime p q h]

/-! ## Auxiliary facts about the Galois action on places -/

private lemma smul_eq_comap_symm_algEquiv {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (σ : K' ≃ₐ[K] K') (A : ValuationSubring K') :
    σ • A = A.comap (σ.symm : K' →+* K') := by
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists, ValuationSubring.mem_comap]
  constructor
  · rintro ⟨s, hs, rfl⟩
    change σ.symm (σ s) ∈ A
    rw [AlgEquiv.symm_apply_apply]
    exact hs
  · intro hh
    exact ⟨σ.symm x, hh, σ.apply_symm_apply x⟩

/-- An element of `Gal(K'/K)` fixing an intermediate field `L` pointwise does not move the trace of
a place of `K'` on `L`. -/
private lemma smul_comap_eq_of_mem_fixingSubgroup {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (L : IntermediateField K K') (g : Gal(K'/K)) (hg : g ∈ L.fixingSubgroup)
    (A : ValuationSubring K') :
    (g • A).comap (algebraMap ↥L K') = A.comap (algebraMap ↥L K') := by
  have hmem : ∀ y ∈ (L : Set K'), g⁻¹ y = y := by
    have h1 : g⁻¹ ∈ L.fixingSubgroup := L.fixingSubgroup.inv_mem hg
    intro y hy
    exact (IntermediateField.mem_fixingSubgroup_iff L g⁻¹).mp h1 y hy
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_comap]
  change g⁻¹ (algebraMap ↥L K' x) ∈ A ↔ algebraMap ↥L K' x ∈ A
  rw [hmem (algebraMap ↥L K' x) x.2]

/-- **Injectivity of the level prime of the place correspondence, for an arbitrary finite level.**

If the image places `a.placeMap A`, `a.placeMap A'` of two places of `K₁'` cut out the same prime
of the corresponding level `levelMap ϕ L`, then `A` and `A'` have the same trace on `L`.  This is
`NK.ReconstructField.comap_eq_of_primeOfLevel_placeMap_eq` with the normality hypothesis on `L`
dropped: the proof only uses the transitivity of the Galois action on the extensions of a place and
the Galois correspondence of levels `(levelMap ϕ L).fixingSubgroup = ϕ(Gal(K₁'/L))`. -/
theorem comap_eq_of_primeOfLevel_placeMap_eq_gen {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [NumberField ↥L]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)] [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    (A A' : NK.Reconstruct.FinitePlaceOf K₁ K₁')
    (h : NK.Reconstruct.primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)) =
      NK.Reconstruct.primeOfLevel (a.placeMap A').1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A').2 (NK.Reconstruct.levelMap ϕ L))) :
    A.1.comap (algebraMap ↥L K₁') = A'.1.comap (algebraMap ↥L K₁') := by
  have hBT : (a.placeMap A).1.comap (algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂') =
      (a.placeMap A').1.comap (algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂') := by
    rw [NK.Reconstruct.primeOfLevel_spec (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
          (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)),
        NK.Reconstruct.primeOfLevel_spec (a.placeMap A').1 (NK.Reconstruct.levelMap ϕ L)
          (NK.Reconstruct.comap_level_ne_top (a.placeMap A').2 (NK.Reconstruct.levelMap ϕ L)), h]
  obtain ⟨σ, hσfix, hσB⟩ := Commons.FieldTheory.Galois.exists_restrictScalars_smul_eq_of_comap_eq
    (K := K₂) (K' := K₂') (NK.Reconstruct.levelMap ϕ L) (a.placeMap A).1 (a.placeMap A').1
    (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)) hBT
  obtain ⟨g, hgL, hgσ⟩ : ∃ g ∈ L.fixingSubgroup, ϕ g = σ := by
    have hfix : σ ∈ (NK.Reconstruct.levelMap ϕ L).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hσfix ⟨x, hx⟩
    rw [NK.Reconstruct.fixingSubgroup_levelMap hϕ L] at hfix
    exact Subgroup.mem_map.mp hfix
  have hplace : NK.Reconstruct.placeSmul₂ (ϕ g) (a.placeMap A) = a.placeMap A' := by
    have h1 : σ • (a.placeMap A).1 = (a.placeMap A').1 := by
      rw [smul_eq_comap_symm_algEquiv σ (a.placeMap A).1, hσB]
    refine Subtype.ext ?_
    rw [NK.Reconstruct.placeSmul₂_val, hgσ]
    exact h1
  have hAeq : NK.Reconstruct.placeSmul g A = A' := by
    apply a.placeMap.injective
    rw [a.map_smul g A, hplace]
  have hval : g • A.1 = A'.1 := congrArg Subtype.val hAeq
  rw [← hval]
  exact (smul_comap_eq_of_mem_fixingSubgroup L g hgL A.1).symm

/-! ## The counting statement -/

/-- **The number of primes above corresponding primes is preserved at corresponding levels**
(CoNF XII §12.2, finite-level counting form, general levels).

Let `L ⊆ K₁'` be a finite normal level which is a number field, `L' ⊇ L` a finite level which is a
number field, and `levelMap ϕ L ⊆ levelMap ϕ L'` the corresponding levels of `K₂'`.  Then for every
prime `𝔭` of `𝓞 L`, the number of primes of `𝓞 L'` above `𝔭` equals the number of primes of
`𝓞 (levelMap ϕ L')` above `levelPrimeMap ϕ hϕ a L 𝔭`.

The proof exhibits an explicit bijection of the two sets of primes: a prime `Q` of `𝓞 L'` over `𝔭`
is sent to the prime of `𝓞 (levelMap ϕ L')` cut out by the image under the place correspondence `a`
of a place of `K₁'` above `Q`.  Membership in the target is the bridge
`liesOver_of_comap_eq_valRing`; injectivity is the general injectivity
`comap_eq_of_primeOfLevel_placeMap_eq_gen`; surjectivity inverts the construction, using the
normality of `L` (the normal-level injectivity `comap_eq_of_primeOfLevel_placeMap_eq`) to identify
the preimage prime at the base level. -/
theorem ncard_primesOver_levelPrimeMapGen {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (L' : IntermediateField K₁ K₁') [FiniteDimensional K₁ L'] [NumberField ↥L'] (hLL' : L ≤ L')
    [Algebra ↥L ↥L'] [IsScalarTower K₁ ↥L ↥L']
    (hincl : ∀ x : ↥L, algebraMap ↥L ↥L' x = (⟨(x : K₁'), hLL' x.2⟩ : ↥L'))
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L')]
    [Algebra ↥(NK.Reconstruct.levelMap ϕ L) ↥(NK.Reconstruct.levelMap ϕ L')]
    [IsScalarTower K₂ ↥(NK.Reconstruct.levelMap ϕ L) ↥(NK.Reconstruct.levelMap ϕ L')]
    (hincl₂ : ∀ y : ↥(NK.Reconstruct.levelMap ϕ L),
      algebraMap ↥(NK.Reconstruct.levelMap ϕ L) ↥(NK.Reconstruct.levelMap ϕ L') y =
        (⟨(y : K₂'), NK.Reconstruct.levelMap_mono ϕ hLL' y.2⟩ : ↥(NK.Reconstruct.levelMap ϕ L')))
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L) :
    (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L')).ncard =
      (((NK.ReconstructField.levelPrimeMap ϕ hϕ a L 𝔭).asIdeal).primesOver
        (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L'))).ncard := by
  classical
  haveI : IsGalois K₁ K₁' := IsSepClosure.isGalois
  haveI : IsGalois K₂ K₂' := IsSepClosure.isGalois
  -- the scalar tower structures induced by the inclusion hypotheses
  haveI hST₁ : IsScalarTower ↥L ↥L' K₁' :=
    isScalarTower_of_inclusion K₁ K₁' L L' hLL' hincl
  haveI hST₂ : IsScalarTower ↥(NK.Reconstruct.levelMap ϕ L) ↥(NK.Reconstruct.levelMap ϕ L') K₂' :=
    isScalarTower_of_inclusion K₂ K₂' (NK.Reconstruct.levelMap ϕ L)
      (NK.Reconstruct.levelMap ϕ L') (NK.Reconstruct.levelMap_mono ϕ hLL') hincl₂
  -- the induced prime of the image level
  set 𝔮 := NK.ReconstructField.levelPrimeMap ϕ hϕ a L 𝔭 with h𝔮def
  -- a place of `K₁'` over `𝔭`
  let A₀ : NK.Reconstruct.FinitePlaceOf K₁ K₁' := placeOverPrime L 𝔭
  have hA₀ : A₀.1.comap (algebraMap ↥L K₁') = valR[↥L, 𝔭] := placeOverPrime_spec L 𝔭
  have h𝔮 : 𝔮 = primeOfLevel (a.placeMap A₀).1 (NK.Reconstruct.levelMap ϕ L)
      (comap_level_ne_top (a.placeMap A₀).2 (NK.Reconstruct.levelMap ϕ L)) := by
    rw [h𝔮def]
    exact levelPrimeMap_spec ϕ hϕ a L 𝔭 A₀ hA₀
  -- membership in either `primesOver` set forces the ideal to be nonzero
  have hne₁ : ∀ Q : Ideal (NumberField.RingOfIntegers ↥L'),
      Q ∈ 𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L') → Q ≠ ⊥ :=
    fun Q hQ => Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot hQ
  have hne₂ : ∀ R : Ideal (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L')),
      R ∈ 𝔮.asIdeal.primesOver
        (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L')) → R ≠ ⊥ :=
    fun R hR => Ideal.ne_bot_of_mem_primesOver 𝔮.ne_bot hR
  -- the map on primes: send `Q` to the prime cut out by the image of a place above `Q`
  let Φ : (Q : Ideal (NumberField.RingOfIntegers ↥L')) →
      Q ∈ 𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L') →
      Ideal (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L')) :=
    fun Q hQ => primeOfLevel (a.placeMap (placeOverPrime L' ⟨Q, hQ.1, hne₁ Q hQ⟩)).1
      (NK.Reconstruct.levelMap ϕ L')
      (comap_level_ne_top (a.placeMap (placeOverPrime L' ⟨Q, hQ.1, hne₁ Q hQ⟩)).2
        (NK.Reconstruct.levelMap ϕ L'))
  refine Set.ncard_congr Φ ?_ ?_ ?_
  · -- the image of a prime over `𝔭` is a prime over `𝔮`
    intro Q hQ
    let Q₀ : NK.Chebotarev.PrimeIdeal ↥L' := ⟨Q, hQ.1, hne₁ Q hQ⟩
    let A : NK.Reconstruct.FinitePlaceOf K₁ K₁' := placeOverPrime L' Q₀
    have hA : A.1.comap (algebraMap ↥L' K₁') = valR[↥L', Q₀] := placeOverPrime_spec L' Q₀
    show (primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L')
      (comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L'))).asIdeal ∈
      𝔮.asIdeal.primesOver (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L'))
    refine ⟨(primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L')
      (comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L'))).isPrime, ?_⟩
    -- the trace of `A` on `L` is the valuation ring of `𝔭`
    have hAL : A.1.comap (algebraMap ↥L K₁') = valR[↥L, 𝔭] :=
      comap_eq_valRing_of_liesOver 𝔭 Q₀ A.1 hA hQ.2
    -- hence the prime cut out at the image level is `𝔮`
    have hlev : primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
        (comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)) = 𝔮 := by
      rw [h𝔮]
      exact primeOfLevel_placeMap_eq_of_comap_eq ϕ hϕ a L A A₀ (by rw [hAL, hA₀])
    exact liesOver_of_comap_eq_valRing 𝔮 (primeOfLevel (a.placeMap A).1
        (NK.Reconstruct.levelMap ϕ L')
        (comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L'))) (a.placeMap A).1
      (primeOfLevel_spec (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L')
        (comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L')))
      ((primeOfLevel_spec (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
        (comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L))).trans
        (congrArg (fun P => valR[↥(NK.Reconstruct.levelMap ϕ L), P]) hlev))
  · -- injectivity
    intro Q Q' hQ hQ' hEq
    let Q₀ : NK.Chebotarev.PrimeIdeal ↥L' := ⟨Q, hQ.1, hne₁ Q hQ⟩
    let Q₀' : NK.Chebotarev.PrimeIdeal ↥L' := ⟨Q', hQ'.1, hne₁ Q' hQ'⟩
    let A : NK.Reconstruct.FinitePlaceOf K₁ K₁' := placeOverPrime L' Q₀
    let A' : NK.Reconstruct.FinitePlaceOf K₁ K₁' := placeOverPrime L' Q₀'
    have hA : A.1.comap (algebraMap ↥L' K₁') = valR[↥L', Q₀] := placeOverPrime_spec L' Q₀
    have hA' : A'.1.comap (algebraMap ↥L' K₁') = valR[↥L', Q₀'] := placeOverPrime_spec L' Q₀'
    have hEqI : (primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L')
        (comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L'))).asIdeal =
        (primeOfLevel (a.placeMap A').1 (NK.Reconstruct.levelMap ϕ L')
        (comap_level_ne_top (a.placeMap A').2 (NK.Reconstruct.levelMap ϕ L'))).asIdeal := hEq
    have hEq' : primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L')
        (comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L')) =
        primeOfLevel (a.placeMap A').1 (NK.Reconstruct.levelMap ϕ L')
        (comap_level_ne_top (a.placeMap A').2 (NK.Reconstruct.levelMap ϕ L')) :=
      IsDedekindDomain.HeightOneSpectrum.ext hEqI
    have hgen := comap_eq_of_primeOfLevel_placeMap_eq_gen ϕ hϕ a L' A A' hEq'
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
      (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥L')
        (hA.symm.trans (hgen.trans hA')))
  · -- surjectivity
    intro R hR
    have hRne : R ≠ ⊥ := hne₂ R hR
    -- a place of `K₂'` above `R`, and the prime it cuts out at the image level
    let R₀ : NK.Chebotarev.PrimeIdeal ↥(NK.Reconstruct.levelMap ϕ L') := ⟨R, hR.1, hRne⟩
    let B : NK.Reconstruct.FinitePlaceOf K₂ K₂' :=
      placeOverPrime (NK.Reconstruct.levelMap ϕ L') R₀
    have hB : B.1.comap (algebraMap ↥(NK.Reconstruct.levelMap ϕ L') K₂') =
        valR[↥(NK.Reconstruct.levelMap ϕ L'), R₀] :=
      placeOverPrime_spec (NK.Reconstruct.levelMap ϕ L') R₀
    have hBR : primeOfLevel B.1 (NK.Reconstruct.levelMap ϕ L')
        (comap_level_ne_top B.2 (NK.Reconstruct.levelMap ϕ L')) = R₀ :=
      primeOfLevel_placeOverPrime (NK.Reconstruct.levelMap ϕ L') R₀
    -- the trace of `B` on the smaller image level is the valuation ring of `𝔮`
    have hBL₂ : B.1.comap (algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂') =
        valR[↥(NK.Reconstruct.levelMap ϕ L), 𝔮] :=
      comap_eq_valRing_of_liesOver 𝔮 R₀ B.1 hB hR.2
    have hlevB : primeOfLevel B.1 (NK.Reconstruct.levelMap ϕ L)
        (comap_level_ne_top B.2 (NK.Reconstruct.levelMap ϕ L)) = 𝔮 :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
        (K := ↥(NK.Reconstruct.levelMap ϕ L))
        ((primeOfLevel_spec B.1 (NK.Reconstruct.levelMap ϕ L)
          (comap_level_ne_top B.2 (NK.Reconstruct.levelMap ϕ L))).symm.trans hBL₂)
    -- the preimage place and the prime of `𝓞 L'` it cuts out
    let A : NK.Reconstruct.FinitePlaceOf K₁ K₁' := a.placeMap.symm B
    have hmapA : a.placeMap A = B := Equiv.apply_symm_apply a.placeMap B
    let Q : NK.Chebotarev.PrimeIdeal ↥L' := primeOfLevel A.1 L' (comap_level_ne_top A.2 L')
    have hQspec : A.1.comap (algebraMap ↥L' K₁') = valR[↥L', Q] := primeOfLevel_spec A.1 L' _
    have hlevA : primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
        (comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)) = 𝔮 :=
      (primeOfLevel_place_congr hmapA).trans hlevB
    -- hence `A` restricts to the valuation ring of `𝔭` on `L`, and `Q` lies over `𝔭`
    have hAL : A.1.comap (algebraMap ↥L K₁') = valR[↥L, 𝔭] := by
      have h2 := comap_eq_of_primeOfLevel_placeMap_eq ϕ hϕ a L A A₀ (hlevA.trans h𝔮.symm)
      exact h2.trans hA₀
    have hQl : Q.asIdeal.LiesOver 𝔭.asIdeal := liesOver_of_comap_eq_valRing 𝔭 Q A.1 hQspec hAL
    have hQl' : Q.asIdeal.LiesOver 𝔭.asIdeal := hQl
    refine ⟨Q, ⟨Q.isPrime, hQl'⟩, ?_⟩
    -- the value of `Φ` at `Q` is `R`
    show (primeOfLevel (a.placeMap (placeOverPrime L' ⟨Q, Q.isPrime, hne₁ Q ⟨Q.isPrime, hQl'⟩⟩)).1
      (NK.Reconstruct.levelMap ϕ L')
      (comap_level_ne_top (a.placeMap (placeOverPrime L' ⟨Q, Q.isPrime,
        hne₁ Q ⟨Q.isPrime, hQl'⟩⟩)).2 (NK.Reconstruct.levelMap ϕ L'))).asIdeal = R
    have hspec' : (placeOverPrime L' ⟨Q, Q.isPrime, hne₁ Q ⟨Q.isPrime, hQl'⟩⟩).1.comap
        (algebraMap ↥L' K₁') = valR[↥L', Q] :=
      placeOverPrime_spec L' ⟨Q, Q.isPrime, hne₁ Q ⟨Q.isPrime, hQl'⟩⟩
    have hsame_comap : (placeOverPrime L' ⟨Q, Q.isPrime, hne₁ Q ⟨Q.isPrime, hQl'⟩⟩).1.comap
        (algebraMap ↥L' K₁') = A.1.comap (algebraMap ↥L' K₁') := hspec'.trans hQspec.symm
    have hsame : primeOfLevel (a.placeMap (placeOverPrime L'
          ⟨Q, Q.isPrime, hne₁ Q ⟨Q.isPrime, hQl'⟩⟩)).1 (NK.Reconstruct.levelMap ϕ L')
        (comap_level_ne_top (a.placeMap (placeOverPrime L'
          ⟨Q, Q.isPrime, hne₁ Q ⟨Q.isPrime, hQl'⟩⟩)).2 (NK.Reconstruct.levelMap ϕ L')) =
        primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L')
        (comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L')) :=
      primeOfLevel_placeMap_eq_of_comap_eq_gen ϕ hϕ a L' _ A hsame_comap
    rw [hsame]
    have hmapA' : primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L')
        (comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L')) =
        primeOfLevel B.1 (NK.Reconstruct.levelMap ϕ L')
        (comap_level_ne_top B.2 (NK.Reconstruct.levelMap ϕ L')) := primeOfLevel_place_congr hmapA
    rw [hmapA']
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hBR

end NK.ReconstructField
