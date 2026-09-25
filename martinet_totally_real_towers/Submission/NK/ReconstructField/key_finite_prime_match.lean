import Mathlib
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.ReconstructField.exists_restrict_of_levelIso
import Submission.NK.ReconstructField.LevelPrime
import Submission.NK.ReconstructField.LevelPrimeBijective
import Submission.NK.ReconstructField.ncard_primesOver_levelPrimeMapGen
import Submission.NK.ReconstructField.eq_of_isNormal_of_algEquiv
import Submission.NK.UchidaKummer.Kummer.machinery_of_isPrimitiveRoot
import Submission.NK.UchidaKummer.Differentiation.isDifferentiable_of_kummerMachinery
import Submission.NK.UchidaKummer.API.localDeg_tower
import Submission.NK.LocalInputs.Defs
import Submission.NK.Reconstruct.Transport
import Submission.NK.ReconstructField.localDegree_primeTransport
import Submission.NK.ReconstructField.conjRingEquiv_eq_levelMapEquiv_of_primeTransport_eq
import Submission.NK.ReconstructField.finrank_tower_eq_of_ringEquiv
import Submission.NK.ReconstructField.localDeg_primeTransport_nested
import Submission.NK.ReconstructField.sum_localDeg_primesOver
import Submission.NK.ReconstructField.primeBelowNat_levelPrimeMap

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.ReconstructField

open NK.Reconstruct

/-! ## Helper lemmas proved in this file -/

/-- The rational prime below a finite prime is determined by `primeBelowNat`. -/
lemma primeBelow_eq_of_primeBelowNat_eq {K : Type*} [Field K] [NumberField K]
    {P Q : NK.Chebotarev.PrimeIdeal K}
    (h : NK.LocalInputs.primeBelowNat K P = NK.LocalInputs.primeBelowNat K Q) :
    NK.LocalInputs.primeBelow K P = NK.LocalInputs.primeBelow K Q := by
  have h2 : Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow K P) =
      Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow K Q) :=
    Subtype.ext h
  exact Rat.HeightOneSpectrum.primesEquiv.injective h2

/-- **The contraction of a transported prime**: for compatible isomorphisms of two extensions of
number fields, the transport of primes commutes with the contraction to the base fields. -/
lemma under_primeTransport {L₁ L₂ M₁ M₂ : Type*} [Field L₁] [NumberField L₁] [Field L₂]
    [NumberField L₂] [Field M₁] [NumberField M₁] [Field M₂] [NumberField M₂]
    [Algebra L₁ L₂] [Algebra M₁ M₂] (σ : L₂ ≃+* M₂) (τ : L₁ ≃+* M₁)
    (hσ : ∀ x : L₁, σ (algebraMap L₁ L₂ x) = algebraMap M₁ M₂ (τ x))
    (Q : NK.Chebotarev.PrimeIdeal M₂) (P : NK.Chebotarev.PrimeIdeal M₁)
    (hQ : Q.asIdeal.under (NumberField.RingOfIntegers M₁) = P.asIdeal) :
    (NK.Reconstruct.primeTransport σ.symm Q).asIdeal.under (NumberField.RingOfIntegers L₁) =
      (NK.Reconstruct.primeTransport τ.symm P).asIdeal := by
  rw [NK.ReconstructField.primeTransport_asIdeal σ.symm Q,
    NK.ReconstructField.primeTransport_asIdeal τ.symm P]
  have hμ : ∀ x : M₁, σ.symm (algebraMap M₁ M₂ x) = algebraMap L₁ L₂ (τ.symm x) := by
    intro x
    apply σ.injective
    rw [σ.apply_symm_apply, hσ (τ.symm x), τ.apply_symm_apply]
  have hφ := NK.ReconstructField.ringOfIntegersEquiv_algebraMap σ.symm τ.symm hμ
  have hcomp := NK.ReconstructField.comap_map_eq_map_comap
      (NK.Reconstruct.ringOfIntegersEquiv σ.symm)
      (NK.Reconstruct.ringOfIntegersEquiv τ.symm)
      (algebraMap (NumberField.RingOfIntegers M₁) (NumberField.RingOfIntegers M₂))
      (algebraMap (NumberField.RingOfIntegers L₁) (NumberField.RingOfIntegers L₂)) hφ Q.asIdeal
  rw [Ideal.under_def] at hQ ⊢
  rw [← hQ]
  exact hcomp

/-- Arithmetic: `ℓ ^ a * N = ℓ ^ b * N` with `N ≠ 0` and `ℓ ≥ 2` forces `a = b`. -/
lemma pow_eq_of_mul_eq_mul {ℓ a b N : ℕ} (hℓ : 2 ≤ ℓ) (hN : N ≠ 0)
    (h : ℓ ^ a * N = ℓ ^ b * N) : a = b :=
  Nat.pow_right_injective hℓ (Nat.mul_right_cancel (Nat.pos_of_ne_zero hN) h)

/-- **The contraction to `𝓞 ℚ` of a pushed-forward ideal is unchanged**: the induced ring
isomorphism of rings of integers of two number fields is the identity on the images of `𝓞 ℚ`. -/
lemma under_map_ringOfIntegersEquiv_rat {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] (e : A ≃+* B) (I : Ideal (NumberField.RingOfIntegers A)) :
    Ideal.under (NumberField.RingOfIntegers ℚ)
        (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e) I) =
      Ideal.under (NumberField.RingOfIntegers ℚ) I := by
  rw [Ideal.under_def, Ideal.under_def]
  have hrefl : NK.Reconstruct.ringOfIntegersEquiv (RingEquiv.refl ℚ) =
      (RingEquiv.refl (NumberField.RingOfIntegers ℚ)) := by
    ext x
    rw [NK.Reconstruct.ringOfIntegersEquiv_apply]
    rfl
  have hφ : ∀ x : NumberField.RingOfIntegers ℚ,
      (NK.Reconstruct.ringOfIntegersEquiv e)
          (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers A) x) =
        algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers B)
          ((NK.Reconstruct.ringOfIntegersEquiv (RingEquiv.refl ℚ)) x) := by
    intro x
    rw [hrefl]
    exact NK.ReconstructField.ringOfIntegersEquiv_algebraMap e (RingEquiv.refl ℚ)
      (fun q => RingHom.map_rat_algebraMap (e : A →+* B) q) x
  have hcomp := NK.ReconstructField.comap_map_eq_map_comap
    (NK.Reconstruct.ringOfIntegersEquiv e)
    (NK.Reconstruct.ringOfIntegersEquiv (RingEquiv.refl ℚ))
    (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers A))
    (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers B)) hφ I
  rw [hcomp, hrefl]
  exact Ideal.map_id _

/-- **The rational prime below a transported prime is unchanged.** -/
lemma primeBelowNat_primeTransport {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] (e : A ≃+* B) (P : NK.Chebotarev.PrimeIdeal A) :
    NK.LocalInputs.primeBelowNat B (NK.Reconstruct.primeTransport e P) =
      NK.LocalInputs.primeBelowNat A P := by
  have h : NK.LocalInputs.primeBelow B (NK.Reconstruct.primeTransport e P) =
      NK.LocalInputs.primeBelow A P := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    show Ideal.under (NumberField.RingOfIntegers ℚ)
        (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e) P.asIdeal) =
      Ideal.under (NumberField.RingOfIntegers ℚ) P.asIdeal
    exact under_map_ringOfIntegersEquiv_rat e P.asIdeal
  rw [NK.LocalInputs.primeBelowNat, NK.LocalInputs.primeBelowNat, h]

/-- `ncard` of a finite set is the cardinality of its type. -/
lemma ncard_eq_fintypeCard {α : Type*} (s : Set α) [Fintype s] : s.ncard = Fintype.card s := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- The sum of a constant over the fibre of primes above `P`, in terms of `ncard`. -/
lemma sum_localDeg_eq_card_mul {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (P : NK.Chebotarev.PrimeIdeal K) (c : ℕ)
    (h : ∀ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L),
      NK.UchidaKummer.localDeg
        ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P = c) :
    ∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L),
      NK.UchidaKummer.localDeg
        ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P =
      c * (P.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard := by
  have h₁ : (∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L),
      NK.UchidaKummer.localDeg
        ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P) =
      ∑ _Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L), c :=
    Finset.sum_congr rfl (fun Q _ => h Q)
  rw [h₁, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  exact congrArg (fun n => c * n) (ncard_eq_fintypeCard _).symm

/-! ## Temporary copies of the lemmas delegated to the fleet -/







/-! ## The main theorem -/

/-- **The finite prime-matching step of the reconstruction** (the differentiation/pinning step of
Neukirch's Lemma *`α identifies with σ on primes`*, CoNF XII §12.2): for every finite set `S` of
primes of a finite normal level `L` there is a level isomorphism `τ : ↥L ≃+* ↥(levelMap ϕ L)` whose
induced map on primes agrees with the local correspondence `levelPrimeMap ϕ hϕ a L` on `S`. -/
theorem key_finite_prime_match {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
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
  -- ## Step 1: the finite set `R'` of primes of `L` over the rational primes below `S`
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
      primeBelow_eq_of_primeBelowNat_eq hPQ.symm
    rw [← h1]
    exact NK.LocalInputs.primeBelow_liesOver ↥L Q
  -- ## Step 2: enumeration of `R'` and the exponent function
  let idx : (P : NK.Chebotarev.PrimeIdeal ↥L) → P ∈ R' → Fin R'.card :=
    fun P hP => Finset.equivFin R' ⟨P, hP⟩
  let 𝔭 : Fin R'.card → NK.Chebotarev.PrimeIdeal ↥L :=
    fun i => (((Finset.equivFin R').symm i : ↥R') : NK.Chebotarev.PrimeIdeal ↥L)
  have h𝔭idx : ∀ (P : NK.Chebotarev.PrimeIdeal ↥L) (hP : P ∈ R'), 𝔭 (idx P hP) = P := by
    intro P hP
    show (((Finset.equivFin R').symm (Finset.equivFin R' ⟨P, hP⟩) : ↥R') :
      NK.Chebotarev.PrimeIdeal ↥L) = P
    rw [Equiv.symm_apply_apply]
  have h𝔭inj : Function.Injective 𝔭 := by
    intro i j hij
    have h1 : ((Finset.equivFin R').symm i : ↥R') = (Finset.equivFin R').symm j := Subtype.ext hij
    exact (Finset.equivFin R').symm.injective h1
  let aexp : Fin R'.card → ℕ := fun i => (i : ℕ) + 1
  have haexpinj : Function.Injective aexp := by
    intro i j h
    exact Fin.ext (Nat.succ.inj h)
  -- ## Step 3: the differentiation over the base field `↥L`
  have hμL : ∃ ζ : ↥L, IsPrimitiveRoot ζ ℓ := by
    obtain ⟨ζ, hζ⟩ := hμ
    exact ⟨algebraMap K₁ ↥L ζ, hζ.map_of_injective (RingHom.injective _)⟩
  haveI hSepL : IsSepClosure ↥L K₁' := NK.Reconstruct.isSepClosure_level L
  have hDiff : NK.UchidaKummer.IsDifferentiable ↥L K₁' ℓ :=
    NK.UchidaKummer.isDifferentiable_of_exists_isPrimitiveRoot (K := ↥L) (K' := K₁') ℓ hℓ hμL
  obtain ⟨E₀, hE₀fd, hE₀nf, hE₀deg⟩ := hDiff R'.card 𝔭 h𝔭inj aexp
  haveI hE₀fdI : FiniteDimensional ↥L E₀ := hE₀fd
  haveI hE₀nfI : NumberField ↥E₀ := hE₀nf
  -- ## Step 4: `E` as a level over `K₁`, the isomorphism `σ` and its restriction `τ`
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
  obtain ⟨σ⟩ := hlev E
  obtain ⟨τ, hτ⟩ := exists_restrict_of_levelIso ϕ hϕ L E hLE σ ⟨(hlev L).some⟩
  -- ## Step 5: the corresponding level `E₂` and its base `M'`
  let M' : IntermediateField K₂ K₂' := NK.Reconstruct.levelMap ϕ L
  let E₂ : IntermediateField K₂ K₂' := NK.Reconstruct.levelMap ϕ E
  have hmono : M' ≤ E₂ := NK.Reconstruct.levelMap_mono ϕ hLE
  haveI hnfE₂ : NumberField ↥E₂ := by
    have h := NK.Reconstruct.numberField_levelMap hϕ E
    exact h
  haveI hfdE₂ : FiniteDimensional K₂ E₂ := (inferInstance : FiniteDimensional K₂ ↥(NK.Reconstruct.levelMap ϕ E))
  haveI hfdM' : FiniteDimensional K₂ M' := (inferInstance : FiniteDimensional K₂ ↥(NK.Reconstruct.levelMap ϕ L))
  haveI hnfM' : NumberField ↥M' := (inferInstance : NumberField ↥(NK.Reconstruct.levelMap ϕ L))
  let gi : ↥M' →ₐ[K₂] ↥E₂ := IntermediateField.inclusion hmono
  letI hAlgM : Algebra ↥M' ↥E₂ := gi.toRingHom.toAlgebra
  haveI hTowerM : IsScalarTower K₂ ↥M' ↥E₂ := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    exact Subtype.ext rfl
  haveI hfdME : FiniteDimensional ↥M' ↥E₂ :=
    Module.Finite.of_restrictScalars_finite K₂ ↥M' ↥E₂
  have hincl₂ : ∀ y : ↥M', (algebraMap ↥M' ↥E₂) y = ⟨(y : K₂'), hmono y.2⟩ :=
    fun y => Subtype.ext rfl
  -- ## Step 6: the counting lemma and the two fibre sums
  have hcount : ∀ P : NK.Chebotarev.PrimeIdeal ↥L,
      (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard =
        ((NK.ReconstructField.levelPrimeMap ϕ hϕ a L P).asIdeal.primesOver
          (NumberField.RingOfIntegers ↥E₂)).ncard := fun P =>
    ncard_primesOver_levelPrimeMapGen ϕ hϕ a L E hLE hincl₁ hincl₂ P
  have hsumL : ∀ P : NK.Chebotarev.PrimeIdeal ↥L,
      (∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E),
        NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P) =
      Module.finrank ↥L ↥E := fun P => sum_localDeg_primesOver P
  have hsumR : ∀ Q₀ : NK.Chebotarev.PrimeIdeal ↥M',
      (∑ Q : Q₀.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂),
        NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver Q₀.ne_bot Q.2⟩ Q₀) =
      Module.finrank ↥M' ↥E₂ := fun Q₀ => sum_localDeg_primesOver Q₀
  have hτσ : ∀ x : ↥L, σ (algebraMap ↥L ↥E x) = algebraMap ↥M' ↥E₂ (τ x) := by
    intro x
    rw [hincl₁ x, hincl₂ (τ x)]
    exact Subtype.ext (hτ x).symm
  have hfin : Module.finrank ↥L ↥E = Module.finrank ↥M' ↥E₂ :=
    finrank_tower_eq_of_ringEquiv (K := K₁) (L := ↥L) (E := ↥E) (K' := K₂) (L' := ↥M')
      (E' := ↥E₂) σ τ hτσ
  -- ## Step 7: the pinning
  have hmatch : ∀ P ∈ S, NK.Reconstruct.primeTransport τ P =
      NK.ReconstructField.levelPrimeMap ϕ hϕ a L P := by
    intro P hP
    have hPR' : P ∈ R' := hSR' P hP
    set αP : NK.Chebotarev.PrimeIdeal ↥M' :=
      NK.ReconstructField.levelPrimeMap ϕ hϕ a L P with hαP
    set Pt : NK.Chebotarev.PrimeIdeal ↥L := NK.Reconstruct.primeTransport τ.symm αP with hPt
    have hτPt : NK.Reconstruct.primeTransport τ Pt = αP := by
      rw [hPt]
      exact NK.ReconstructField.primeTransport_symm_apply τ αP
    have hPtR' : Pt ∈ R' := by
      refine hR'cl Pt ?_
      rw [hPt, primeBelowNat_primeTransport τ.symm αP, hαP,
        primeBelowNat_levelPrimeMap ϕ hϕ a L P]
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
    have hdegP : ∀ Q : NK.Chebotarev.PrimeIdeal ↥E, Q.asIdeal.LiesOver P.asIdeal →
        NK.UchidaKummer.localDeg Q P = ℓ ^ (aexp (idx P hPR')) := by
      intro Q hQ
      have h := hE₀deg (idx P hPR') Q (by rw [h𝔭idx]; exact hQ)
      rwa [h𝔭idx] at h
    have hdegPt : ∀ Q : NK.Chebotarev.PrimeIdeal ↥E, Q.asIdeal.LiesOver Pt.asIdeal →
        NK.UchidaKummer.localDeg Q Pt = ℓ ^ (aexp (idx Pt hPtR')) := by
      intro Q hQ
      have h := hE₀deg (idx Pt hPtR') Q (by rw [h𝔭idx]; exact hQ)
      rwa [h𝔭idx] at h
    have hdegE₂ : ∀ Q' : αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂),
        NK.UchidaKummer.localDeg
          ⟨Q'.1, Q'.2.1, Ideal.ne_bot_of_mem_primesOver αP.ne_bot Q'.2⟩ αP =
        ℓ ^ (aexp (idx Pt hPtR')) := by
      intro Q'
      set Q'' : NK.Chebotarev.PrimeIdeal ↥E :=
        NK.Reconstruct.primeTransport σ.symm
          ⟨Q'.1, Q'.2.1, Ideal.ne_bot_of_mem_primesOver αP.ne_bot Q'.2⟩ with hQ''def
      have hQ''over : Q''.asIdeal.LiesOver Pt.asIdeal := by
        have h := under_primeTransport σ τ hτσ
          (⟨Q'.1, Q'.2.1, Ideal.ne_bot_of_mem_primesOver αP.ne_bot Q'.2⟩ :
            NK.Chebotarev.PrimeIdeal ↥E₂) αP Q'.2.2.over.symm
        rw [← hPt] at h
        rw [hQ''def]
        exact Ideal.LiesOver.mk h.symm
      have h1 : NK.UchidaKummer.localDeg Q'' Pt = ℓ ^ (aexp (idx Pt hPtR')) :=
        hdegPt Q'' hQ''over
      have h2 : NK.UchidaKummer.localDeg (NK.Reconstruct.primeTransport σ Q'')
          (NK.Reconstruct.primeTransport τ Pt) = NK.UchidaKummer.localDeg Q'' Pt :=
        localDeg_primeTransport_nested σ τ hτσ Q'' Pt hQ''over
      rw [hτPt] at h2
      rw [← h1, ← h2]
      congr 1
      rw [hQ''def, NK.ReconstructField.primeTransport_symm_apply]
    have hP'sum : (∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E),
        NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P) =
        ℓ ^ (aexp (idx P hPR')) * (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard :=
      sum_localDeg_eq_card_mul P _ (fun Q => hdegP ⟨Q.1, Q.2.1,
        Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ Q.2.2)
    have hα'sum : (∑ Q : αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂),
        NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver αP.ne_bot Q.2⟩ αP) =
        ℓ ^ (aexp (idx Pt hPtR')) *
          (αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂)).ncard :=
      sum_localDeg_eq_card_mul αP _ (fun Q => hdegE₂ Q)
    have hcount' : (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard =
        (αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂)).ncard := by
      rw [hαP]
      exact hcount P
    have hkey : ℓ ^ (aexp (idx P hPR')) * (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard =
        ℓ ^ (aexp (idx Pt hPtR')) *
          (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard := by
      calc ℓ ^ (aexp (idx P hPR')) * (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard
          = ∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E),
              NK.UchidaKummer.localDeg
                ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P := hP'sum.symm
        _ = Module.finrank ↥L ↥E := hsumL P
        _ = Module.finrank ↥M' ↥E₂ := hfin
        _ = ∑ Q : αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂),
              NK.UchidaKummer.localDeg
                ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver αP.ne_bot Q.2⟩ αP := (hsumR αP).symm
        _ = ℓ ^ (aexp (idx Pt hPtR')) *
              (αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂)).ncard := hα'sum
        _ = ℓ ^ (aexp (idx Pt hPtR')) *
              (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard := by rw [hcount']
    have hNpos : (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard ≠ 0 := by
      intro h0
      have hpos : 0 < ℓ ^ (aexp (idx P hPR')) *
          (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard := by
        rw [← hP'sum, hsumL P]
        exact Module.finrank_pos
      rw [h0, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    have ha : aexp (idx P hPR') = aexp (idx Pt hPtR') :=
      pow_eq_of_mul_eq_mul hℓ.two_le hNpos hkey
    have hidx : idx P hPR' = idx Pt hPtR' := haexpinj ha
    have hPeq : P = Pt := by
      rw [← h𝔭idx P hPR', ← h𝔭idx Pt hPtR', hidx]
    rw [hPeq, hτPt, hαP]
  -- ## Step 8: conclude
  exact ⟨τ, hmatch⟩

end NK.ReconstructField
