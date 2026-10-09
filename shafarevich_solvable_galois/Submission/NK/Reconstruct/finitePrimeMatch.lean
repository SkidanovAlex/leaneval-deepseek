import Mathlib
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.ReconstructField.LevelPrime
import Submission.NK.ReconstructField.LevelPrimeBijective
import Submission.NK.ReconstructField.eq_of_isNormal_of_algEquiv
import Submission.NK.ReconstructField.ncard_primesOver_levelPrimeMapGen
import Submission.NK.ReconstructField.primeOfLevel_placeMap_eq_of_comap_eq_gen
import Submission.NK.UchidaKummer.Kummer.machinery_of_isPrimitiveRoot
import Submission.NK.UchidaKummer.Differentiation.isDifferentiable_of_kummerMachinery
import Submission.NK.UchidaKummer.Differentiation.kummerStep_multiPrime
import Submission.NK.UchidaKummer.Differentiation.exists_kummerField_localDeg_eq_of_surjective
import Submission.NK.LocalInputs.Defs
import Submission.NK.LocalInputs.ResidueChar.primeBelow_eq_of_liesOver
import Submission.NK.ReconstructField.levelPrimeMap_liesOver
import Submission.NK.ReconstructField.finrank_eq_of_localCorrespondence
import Submission.NK.ReconstructField.conjRingEquiv_eq_levelMapEquiv_of_primeTransport_eq
import Submission.Commons.NumberTheory.NumberField.finite_primesOver
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.NK.Reconstruct.levelIsoRestrict
import Submission.NK.Reconstruct.ncard_primesOver_map_ringEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open IsDedekindDomain

namespace NK.Reconstruct

noncomputable section

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-! ## 1. The fundamental identity in the fibre form -/

theorem sum_localDeg_primesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (P : NK.Chebotarev.PrimeIdeal K) :
    ∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L),
      NK.UchidaKummer.localDeg
        ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P = Module.finrank K L := by
  have hfin : (P.asIdeal.primesOver (NumberField.RingOfIntegers L)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver P.asIdeal P.isPrime P.ne_bot
  letI : Fintype (P.asIdeal.primesOver (NumberField.RingOfIntegers L)) := hfin.fintype
  have h := Ideal.sum_ramification_inertia_eq_finrank (p := P.asIdeal)
    (S := NumberField.RingOfIntegers L)
  rw [IsFractionRing.finrank_eq (NumberField.RingOfIntegers K) K (NumberField.RingOfIntegers L) L]
  rw [← h]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rfl

theorem ncard_primesOver_mul_eq_finrank {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (P : NK.Chebotarev.PrimeIdeal K)
    (d : ℕ)
    (h : ∀ Q : NK.Chebotarev.PrimeIdeal L, Q.asIdeal.LiesOver P.asIdeal →
      NK.UchidaKummer.localDeg Q P = d) :
    (P.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard * d = Module.finrank K L := by
  have hfin : (P.asIdeal.primesOver (NumberField.RingOfIntegers L)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver P.asIdeal P.isPrime P.ne_bot
  letI : Fintype (↥(P.asIdeal.primesOver (NumberField.RingOfIntegers L))) := hfin.fintype
  have hsum := sum_localDeg_primesOver (K := K) (L := L) P
  have hconst : (∑ Q : ↥(P.asIdeal.primesOver (NumberField.RingOfIntegers L)),
      NK.UchidaKummer.localDeg
        ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P) = Fintype.card
        ↥(P.asIdeal.primesOver (NumberField.RingOfIntegers L)) * d := by
    rw [Finset.sum_congr rfl (fun Q _ => h ⟨Q.1, Q.2.1, _⟩ Q.2.2)]
    simp
  rw [hconst] at hsum
  rw [← hsum, Set.fintypeCard_eq_ncard]

theorem ncard_primesOver_ne_zero {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (P : NK.Chebotarev.PrimeIdeal K) :
    (P.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard ≠ 0 := by
  obtain ⟨Q, hQ⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := K) (L := L) P
  have hmem : Q.asIdeal ∈ P.asIdeal.primesOver (NumberField.RingOfIntegers L) :=
    ⟨Q.isPrime, hQ⟩
  have hfin : (P.asIdeal.primesOver (NumberField.RingOfIntegers L)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver P.asIdeal P.isPrime P.ne_bot
  have hpos : 0 < (P.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard :=
    (Set.ncard_pos hfin).mpr ⟨Q.asIdeal, hmem⟩
  omega

/-! ## 2. The rational prime below a prime is preserved by the correspondences -/

lemma primeBelow_eq_of_primeBelowNat_eqAlt {K : Type*} [Field K] [NumberField K]
    (𝔭 𝔭' : NK.Chebotarev.PrimeIdeal K)
    (h : NK.LocalInputs.primeBelowNat K 𝔭 = NK.LocalInputs.primeBelowNat K 𝔭') :
    NK.LocalInputs.primeBelow K 𝔭 = NK.LocalInputs.primeBelow K 𝔭' :=
  Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext h)

/-- **The map on rings of integers induced by a ring isomorphism of number fields commutes with the
structure maps from `𝓞 ℚ`.** -/
lemma ringOfIntegersEquiv_rat_compat {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] (e : A ≃+* B) :
    ((NK.Reconstruct.ringOfIntegersEquiv e :
      NumberField.RingOfIntegers A →+* NumberField.RingOfIntegers B)).comp
      (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers A)) =
      algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers B) := by
  ext z
  obtain ⟨n, rfl⟩ := Rat.int_algebraMap_surjective (R := NumberField.RingOfIntegers ℚ) z
  rw [RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply ℤ (NumberField.RingOfIntegers ℚ)
      (NumberField.RingOfIntegers A)]
  rw [show ((NK.Reconstruct.ringOfIntegersEquiv e :
        NumberField.RingOfIntegers A →+* NumberField.RingOfIntegers B))
      (algebraMap ℤ (NumberField.RingOfIntegers A) n) =
      algebraMap ℤ (NumberField.RingOfIntegers B) n from by
    simpa only [algebraMap_int_eq, Int.coe_castRingHom] using
      map_intCast (NK.Reconstruct.ringOfIntegersEquiv e :
        NumberField.RingOfIntegers A →+* NumberField.RingOfIntegers B) n]
  rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.RingOfIntegers ℚ)
    (NumberField.RingOfIntegers B)]

/-- **The rational prime below a transported prime is the same.** -/
lemma under_rat_map_ringOfIntegersEquiv {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] (e : A ≃+* B) (I : Ideal (NumberField.RingOfIntegers A)) :
    (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e) I).under
        (NumberField.RingOfIntegers ℚ) =
      I.under (NumberField.RingOfIntegers ℚ) := by
  refine Ideal.ext (fun z => ?_)
  rw [Ideal.mem_comap, Ideal.mem_comap, ← ringOfIntegersEquiv_rat_compat e, RingHom.comp_apply]
  exact Ideal.apply_mem_of_equiv_iff

lemma primeBelow_primeTransport {A B : Type*} [Field A] [NumberField A] [Field B] [NumberField B]
    (e : A ≃+* B) (P : NK.Chebotarev.PrimeIdeal A) :
    NK.LocalInputs.primeBelow B (NK.Reconstruct.primeTransport e P) =
      NK.LocalInputs.primeBelow A P := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  show (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e) P.asIdeal).under
      (NumberField.RingOfIntegers ℚ) = P.asIdeal.under (NumberField.RingOfIntegers ℚ)
  exact under_rat_map_ringOfIntegersEquiv e P.asIdeal

/-- **The rational prime below a prime of an extension is the prime below its trace.** -/
lemma primeBelow_under_eq {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (P : NK.Chebotarev.PrimeIdeal L) :
    NK.LocalInputs.primeBelow L P =
      NK.LocalInputs.primeBelow K
        (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) P) := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NK.LocalInputs.primeBelow_asIdeal L P,
    NK.LocalInputs.primeBelow_asIdeal K
      (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) P),
    IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]

/-- **The local correspondence preserves the rational prime below a prime.** -/
lemma primeBelow_primeMap {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (𝔭 : NK.Chebotarev.PrimeIdeal K₁) :
    NK.LocalInputs.primeBelow K₂ (a.primeMap 𝔭) =
      NK.LocalInputs.primeBelow K₁ 𝔭 :=
  NK.LocalInputs.ResidueChar.primeBelow_eq_of_liesOver (a.primeMap 𝔭)
    (NK.LocalInputs.primeBelow K₁ 𝔭)
    (NK.ReconstructField.liesOver_of_charP (a.primeMap 𝔭) (NK.LocalInputs.primeBelow K₁ 𝔭)
      (NK.ReconstructField.charP_primeMap a 𝔭 _
        (NK.ReconstructField.charP_of_liesOver 𝔭 (NK.LocalInputs.primeBelow K₁ 𝔭)
          (NK.LocalInputs.primeBelow_liesOver K₁ 𝔭))))

lemma primeBelow_levelPrimeMap (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (P : NK.Chebotarev.PrimeIdeal ↥L) :
    NK.LocalInputs.primeBelow ↥(NK.Reconstruct.levelMap ϕ L)
        (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P) =
      NK.LocalInputs.primeBelow ↥L P := by
  set 𝔭 : NK.Chebotarev.PrimeIdeal K₁ :=
    IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K₁) P with h𝔭
  have hP : P.asIdeal.LiesOver 𝔭.asIdeal := by
    rw [h𝔭, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    exact Ideal.over_under P.asIdeal
  have htr : IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K₂)
        (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P) = a.primeMap 𝔭 := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    exact (NK.ReconstructField.levelPrimeMap_liesOver ϕ hϕ a L 𝔭 P hP).over.symm
  rw [primeBelow_under_eq (K := K₂) (L := ↥(NK.Reconstruct.levelMap ϕ L))
      (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P),
    htr, primeBelow_primeMap a 𝔭, ← primeBelow_under_eq (K := K₁) (L := ↥L) P]

/-! ## 3. The prime transport of an isomorphism and its inverse -/

/-! ## 4. The theorem -/

/-- Finite-set form of the Kummer-theoretic prime identification (Uchida/Shimizu,
`lem:alpha identifies with sigma on primes`, restricted to a finite set of primes).  Same statement
as `NK.Reconstruct.keyFinitePrimeMatch` (and as the sibling
`NK.ReconstructField.key_finite_prime_match`).

There is a single isomorphism `τ : ↥L ≃+* ↥(levelMap ϕ L)` of the level whose induced prime map
agrees with the prime correspondence `levelPrimeMap ϕ hϕ a L` on the finite set `S`.

**Proof (the counting route, which avoids the relative local-degree comparison).**

1.  Enlarge `S` to the finite set `R'` of all primes of `𝓞 L` lying over the rational primes below
    the primes of `S`.
2.  By `NK.UchidaKummer.isDifferentiable_of_exists_isPrimitiveRoot` for the base field `↥L`
    (`μ_ℓ ⊆ K₁ ⊆ L`, from `hμ`) and `hℓ`, applied to the primes of `R'` with *pairwise distinct*
    exponents, one obtains a finite level `E₀ ⊇ L` (a number field) such that every prime of `E₀`
    above a prime `Q ∈ R'` has relative local degree `ℓ ^ a_Q` (`NK.UchidaKummer.HasLocalDegrees`).
3.  `hlev` gives `e : ↥E ≃+* ↥(levelMap ϕ E)` for the level `E = E₀.restrictScalars K₁`, and
    `NK.Reconstruct.levelIsoRestrict` (proved by a colleague in this workspace) shows that `e`
    carries `L` onto `levelMap ϕ L`; its restriction is `τ : ↥L ≃+* ↥(levelMap ϕ L)`.
4.  For a prime `P` of `𝓞 L` let `n P` be the number of primes of `𝓞 E` above `P`, and
    `f X` the number of primes of `𝓞 (levelMap ϕ E)` above a prime `X` of `𝓞 (levelMap ϕ L)`.  Then
    `n P = f (levelPrimeMap ϕ hϕ a L P)` (`ncard_primesOver_levelPrimeMapGen`) and also
    `n P = f (primeTransport τ P)` (the fibre transport `ncard_primesOver_map_ringEquiv`, applied to
    the isomorphism `e` of extensions).  Hence the permutation `Ψ := primeTransport τ.symm ∘
    levelPrimeMap ϕ hϕ a L` of the primes of `𝓞 L` satisfies `n (Ψ P) = n P`.
5.  By the fundamental identity for the extension `E / L`
    (`Ideal.sum_ramification_inertia_eq_finrank`, packaged as
    `ncard_primesOver_mul_eq_finrank`) and the prescribed degrees, for `P ∈ R'` one has
    `n P * ℓ ^ a_P = [E : L]`, whence `n` is injective on `R'` (the exponents are pairwise distinct
    and `n P ≠ 0`).
6.  `Ψ` preserves the rational prime below a prime (the residue characteristic is preserved by `a` —
    `NK.Reconstruct.LocalCorrespondence.residueChar` — and by the field isomorphism), so `Ψ` maps
    `R'` into `R'`.  For `P ∈ S` this gives
    `ℓ ^ a_{Ψ P} * n (Ψ P) = [E : L] = ℓ ^ a_P * n P`, hence `a_{Ψ P} = a_P` and so `Ψ P = P`, i.e.
    `primeTransport τ P = levelPrimeMap ϕ hϕ a L P`. -/
theorem finitePrimeMatch {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ℓ : ℕ}
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    [IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ L)]
    (S : Finset (NK.Chebotarev.PrimeIdeal ↥L)) :
    ∃ τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L),
      ∀ P ∈ S, NK.Reconstruct.primeTransport τ P =
        NK.ReconstructField.levelPrimeMap ϕ hϕ a L P := by
  classical
  -- ## (0) the Kummer hypotheses
  have hμL : ∃ ζ : ↥L, IsPrimitiveRoot ζ ℓ := by
    obtain ⟨ζ, hζ⟩ := hμ
    exact ⟨algebraMap K₁ ↥L ζ, hζ.map_of_injective (RingHom.injective _)⟩
  haveI hSepL : IsSepClosure ↥L K₁' := ⟨IsSepClosure.sep_closed K₁, inferInstance⟩
  have hDiff : NK.UchidaKummer.IsDifferentiable ↥L K₁' ℓ :=
    NK.UchidaKummer.isDifferentiable_of_exists_isPrimitiveRoot (K := ↥L) (K' := K₁') ℓ hℓ hμL
  -- ## (1) the enlarged finite set `R'`
  let R' : Finset (NK.Chebotarev.PrimeIdeal ↥L) :=
    S.biUnion (fun P => NK.UchidaKummer.Differentiation.primesOverFinset (K := ℚ) (L := ↥L)
      (NK.LocalInputs.primeBelow ↥L P))
  have hSR' : ∀ P ∈ S, P ∈ R' := by
    intro P hP
    refine Finset.mem_biUnion.mpr ⟨P, hP, ?_⟩
    rw [NK.UchidaKummer.Differentiation.mem_primesOverFinset]
    exact NK.LocalInputs.primeBelow_liesOver ↥L P
  have hR'cl : ∀ Q : NK.Chebotarev.PrimeIdeal ↥L,
      NK.LocalInputs.primeBelowNat ↥L Q ∈ S.image (NK.LocalInputs.primeBelowNat ↥L) →
        Q ∈ R' := by
    intro Q hQ
    obtain ⟨P, hP, hPQ⟩ := Finset.mem_image.mp hQ
    refine Finset.mem_biUnion.mpr ⟨P, hP, ?_⟩
    rw [NK.UchidaKummer.Differentiation.mem_primesOverFinset]
    have h1 : NK.LocalInputs.primeBelow ↥L Q = NK.LocalInputs.primeBelow ↥L P :=
      primeBelow_eq_of_primeBelowNat_eqAlt Q P hPQ.symm
    rw [← h1]
    exact NK.LocalInputs.primeBelow_liesOver ↥L Q
  -- ## (2) enumeration of `R'` and pairwise distinct exponents
  let idx : (P : NK.Chebotarev.PrimeIdeal ↥L) → P ∈ R' → Fin R'.card :=
    fun P hP => R'.equivFin ⟨P, hP⟩
  let 𝔭 : Fin R'.card → NK.Chebotarev.PrimeIdeal ↥L :=
    fun i => ((R'.equivFin.symm i : ↥R') : NK.Chebotarev.PrimeIdeal ↥L)
  have h𝔭idx : ∀ (P : NK.Chebotarev.PrimeIdeal ↥L) (hP : P ∈ R'), 𝔭 (idx P hP) = P := by
    intro P hP
    show ((R'.equivFin.symm (R'.equivFin ⟨P, hP⟩) : ↥R') : NK.Chebotarev.PrimeIdeal ↥L) = P
    rw [Equiv.symm_apply_apply]
  have h𝔭inj : Function.Injective 𝔭 := by
    intro i j hij
    exact R'.equivFin.symm.injective (Subtype.ext hij)
  let aexp : Fin R'.card → ℕ := fun i => (i : ℕ) + 1
  have haexpinj : Function.Injective aexp := fun i j h => Fin.ext (Nat.succ.inj h)
  -- ## (3) the differentiation over the base field `↥L`
  obtain ⟨E₀, hE₀fd, hE₀nf, hE₀deg⟩ := hDiff R'.card 𝔭 h𝔭inj aexp
  haveI hE₀fdI : FiniteDimensional ↥L E₀ := hE₀fd
  haveI hE₀nfI : NumberField ↥E₀ := hE₀nf
  -- ## (4) `E` as a level over `K₁` and the restricted isomorphism `τ`
  let E : IntermediateField K₁ K₁' := IntermediateField.restrictScalars K₁ E₀
  have hLE : L ≤ E := by
    intro x hx
    show x ∈ E₀
    exact (bot_le : (⊥ : IntermediateField ↥L K₁') ≤ E₀)
      (IntermediateField.mem_bot.mpr ⟨⟨x, hx⟩, rfl⟩)
  letI hAlgL : Algebra ↥L ↥E := (inferInstance : Algebra ↥L ↥E₀)
  haveI hTowerL : IsScalarTower K₁ ↥L ↥E := (inferInstance : IsScalarTower K₁ ↥L ↥E₀)
  haveI hfdLE : FiniteDimensional ↥L ↥E := (inferInstance : FiniteDimensional ↥L ↥E₀)
  haveI hfdE : FiniteDimensional K₁ E := FiniteDimensional.trans K₁ ↥L ↥E
  haveI hnfE : NumberField ↥E := (inferInstance : NumberField ↥E₀)
  have hincl₁ : ∀ x : ↥L, (algebraMap ↥L ↥E) x = ⟨(x : K₁'), hLE x.2⟩ := fun x => Subtype.ext rfl
  obtain ⟨e⟩ := hlev E
  obtain ⟨τ, hτ⟩ := NK.Reconstruct.levelIsoRestrict ϕ hϕ L E hLE (hlev L) e
  -- ## (5) the corresponding levels and the algebra structure on the image side
  let M' : IntermediateField K₂ K₂' := NK.Reconstruct.levelMap ϕ L
  let E₂ : IntermediateField K₂ K₂' := NK.Reconstruct.levelMap ϕ E
  haveI hnfE₂ : NumberField ↥E₂ := NK.Reconstruct.numberField_levelMap hϕ E
  have hmono : M' ≤ E₂ := NK.Reconstruct.levelMap_mono ϕ hLE
  let gi : ↥M' →ₐ[K₂] ↥E₂ := IntermediateField.inclusion hmono
  letI hAlgM : Algebra ↥M' ↥E₂ := gi.toRingHom.toAlgebra
  have hAlgM_apply : ∀ y : ↥M', (algebraMap ↥M' ↥E₂) y = ⟨(y : K₂'), hmono y.2⟩ :=
    fun y => Subtype.ext rfl
  haveI hTowerM : IsScalarTower K₂ ↥M' ↥E₂ :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  -- ## (6) the two fibre-count identities
  have hcount_c : ∀ P : NK.Chebotarev.PrimeIdeal ↥L,
      (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard =
        ((NK.ReconstructField.levelPrimeMap ϕ hϕ a L P).asIdeal.primesOver
          (NumberField.RingOfIntegers ↥E₂)).ncard := fun P =>
    NK.ReconstructField.ncard_primesOver_levelPrimeMapGen ϕ hϕ a L E hLE hincl₁ hAlgM_apply P
  have hcount_b : ∀ P : NK.Chebotarev.PrimeIdeal ↥L,
      (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard =
        ((NK.Reconstruct.primeTransport τ P).asIdeal.primesOver
          (NumberField.RingOfIntegers ↥E₂)).ncard := by
    intro P
    refine NK.Reconstruct.ncard_primesOver_map_ringEquiv e τ ?_ P
    intro x
    rw [hincl₁ x, hAlgM_apply (τ x)]
    exact Subtype.ext (hτ x).symm
  -- ## (7) the permutation `Ψ` of the primes of `L` and the identity `n (Ψ P) = n P`
  let Ψ : NK.Chebotarev.PrimeIdeal ↥L → NK.Chebotarev.PrimeIdeal ↥L := fun Q =>
    NK.Reconstruct.primeTransport τ.symm (NK.ReconstructField.levelPrimeMap ϕ hϕ a L Q)
  have hnΨ : ∀ P : NK.Chebotarev.PrimeIdeal ↥L,
      ((Ψ P).asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard =
        (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard := by
    intro P
    have h1 := hcount_b (Ψ P)
    have h2 := hcount_c P
    have h3 : NK.Reconstruct.primeTransport τ (Ψ P) =
        NK.ReconstructField.levelPrimeMap ϕ hϕ a L P :=
      NK.ReconstructField.primeTransport_symm_apply τ (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P)
    rw [h1, h3, ← h2]
  -- ## (8) the prescribed local degrees and the resulting count
  have hdegE : ∀ (i : Fin R'.card) (Q : NK.Chebotarev.PrimeIdeal ↥E),
      Q.asIdeal.LiesOver (𝔭 i).asIdeal →
        NK.UchidaKummer.localDeg Q (𝔭 i) = ℓ ^ aexp i :=
    fun i Q hQ => hE₀deg i Q hQ
  have hdegsum𝔭 : ∀ i : Fin R'.card,
      ((𝔭 i).asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard *
        ℓ ^ aexp i = Module.finrank ↥L ↥E := fun i =>
    ncard_primesOver_mul_eq_finrank (K := ↥L) (L := ↥E) (𝔭 i) (ℓ ^ aexp i) (hdegE i)
  have hdegsum : ∀ (P : NK.Chebotarev.PrimeIdeal ↥L) (hP : P ∈ R'),
      (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard *
        ℓ ^ (aexp (idx P hP)) = Module.finrank ↥L ↥E := by
    intro P hP
    have h := hdegsum𝔭 (idx P hP)
    rwa [h𝔭idx P hP] at h
  -- ## (9) the pinning
  refine ⟨τ, fun P hP => ?_⟩
  have hPR' : P ∈ R' := hSR' P hP
  have hPtR' : Ψ P ∈ R' := by
    refine hR'cl (Ψ P) ?_
    have h1 : NK.LocalInputs.primeBelowNat ↥L (Ψ P) =
        NK.LocalInputs.primeBelowNat ↥M' (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P) := by
      rw [show Ψ P = NK.Reconstruct.primeTransport τ.symm
          (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P) from rfl]
      exact congrArg (fun 𝔮 => (Rat.HeightOneSpectrum.primesEquiv 𝔮).1)
        (primeBelow_primeTransport τ.symm (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P))
    have h2 : NK.LocalInputs.primeBelowNat ↥M'
        (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P) =
        NK.LocalInputs.primeBelowNat ↥L P :=
      congrArg (fun 𝔮 => (Rat.HeightOneSpectrum.primesEquiv 𝔮).1)
        (primeBelow_levelPrimeMap ϕ hϕ a L P)
    rw [h1, h2]
    exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
  have h1 := hdegsum P hPR'
  have h2 := hdegsum (Ψ P) hPtR'
  rw [← hnΨ P] at h1
  have hNpos : 0 < ((Ψ P).asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard :=
    Nat.pos_of_ne_zero (ncard_primesOver_ne_zero (K := ↥L) (L := ↥E) (Ψ P))
  have hpow : ℓ ^ (aexp (idx P hPR')) = ℓ ^ (aexp (idx (Ψ P) hPtR')) :=
    Nat.mul_left_cancel hNpos (h1.trans h2.symm)
  have hidx : idx P hPR' = idx (Ψ P) hPtR' :=
    haexpinj (Nat.pow_right_injective hℓ.two_le hpow)
  have hPeq : P = Ψ P := by
    have h1 : 𝔭 (idx P hPR') = 𝔭 (idx (Ψ P) hPtR') := by rw [hidx]
    rw [h𝔭idx P hPR', h𝔭idx (Ψ P) hPtR'] at h1
    exact h1
  have hkey : NK.Reconstruct.primeTransport τ (Ψ P) =
      NK.ReconstructField.levelPrimeMap ϕ hϕ a L P := by
    rw [show Ψ P = NK.Reconstruct.primeTransport τ.symm
        (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P) from rfl]
    exact NK.ReconstructField.primeTransport_symm_apply τ _
  calc NK.Reconstruct.primeTransport τ P = NK.Reconstruct.primeTransport τ (Ψ P) :=
      congrArg (NK.Reconstruct.primeTransport τ) hPeq
    _ = NK.ReconstructField.levelPrimeMap ϕ hϕ a L P := hkey

end
end NK.Reconstruct
