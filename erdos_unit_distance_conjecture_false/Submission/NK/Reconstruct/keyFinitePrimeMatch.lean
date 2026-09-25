import Mathlib
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.ReconstructField.LevelPrime
import Submission.NK.ReconstructField.LevelPrimeBijective
import Submission.NK.ReconstructField.eq_of_isNormal_of_algEquiv
import Submission.NK.ReconstructField.exists_level_galois_image
import Submission.NK.ReconstructField.ncard_primesOver_levelPrimeMapGen
import Submission.NK.ReconstructField.exists_levelIso_restrict
import Submission.NK.ReconstructField.primeBelowNat_levelPrimeMap
import Submission.NK.ReconstructField.eq_of_primeTransport_eq
import Submission.NK.ReconstructField.ncard_primesOver_primeTransport
import Submission.NK.ReconstructField.ncard_primesOver_mul_eq_finrank_of_forall_localDeg
import Submission.NK.LocalInputs.ResidueChar.primeBelow_eq_of_liesOver
import Submission.NK.UchidaKummer.Kummer.machinery_of_isPrimitiveRoot
import Submission.NK.UchidaKummer.Differentiation.isDifferentiable_of_kummerMachinery
import Submission.NK.UchidaKummer.API.localDeg_tower
import Submission.NK.UchidaKummer.API.isKummerSurjective_mono

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace NK.Reconstruct

open NK

section Helpers

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K']

/-- **An intermediate field over `↥L` is an intermediate field over `K`.**  The carrier is the
same set, so the two subtypes are definitionally equal. -/
noncomputable def toKi (L : IntermediateField K K') (M' : IntermediateField ↥L K') :
    IntermediateField K K' :=
  Subfield.toIntermediateField M'.toSubfield (fun a => by
    have h := IntermediateField.algebraMap_mem M' (algebraMap K ↥L a)
    rw [← IsScalarTower.algebraMap_apply K ↥L K'] at h
    exact h)

/-- `L` is contained in the transported field. -/
theorem le_toKi (L : IntermediateField K K') (M' : IntermediateField ↥L K') : L ≤ toKi L M' := by
  intro y hy
  have h : algebraMap ↥L K' (⟨y, hy⟩ : ↥L) ∈ M' := IntermediateField.algebraMap_mem M' _
  rw [IntermediateField.algebraMap_apply] at h
  exact h

/-- **The `↥L`-algebra structure on `↥M` given by the inclusion**, for `L ≤ M` two intermediate
fields of `K' / K`. -/
noncomputable def algOfLe (L M : IntermediateField K K') (h : L ≤ M) : Algebra ↥L ↥M :=
  RingHom.toAlgebra
    { toFun := fun x => ⟨x.1, h x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }

/-- The scalar tower structure attached to `algOfLe`. -/
theorem isScalarTower_algOfLe (L M : IntermediateField K K') (h : L ≤ M) [Algebra ↥L ↥M]
    (hincl : ∀ x : ↥L, algebraMap ↥L ↥M x = (⟨x.1, h x.2⟩ : ↥M)) : IsScalarTower K ↥L ↥M := by
  refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
  apply Subtype.ext
  simp only [RingHom.comp_apply, hincl]
  rfl

end Helpers


/-- **The rational prime below a transported prime is the prime below.**  The isomorphism
`ringOfIntegersEquiv e : 𝓞 A ≃+* 𝓞 B` induced by a ring isomorphism `e : A ≃+* B` of number fields
is the identity on the (images of the) integers, so contracting an ideal along `𝓞 ℚ → 𝓞 B` after
mapping it forward along `ringOfIntegersEquiv e` is the same as contracting along `𝓞 ℚ → 𝓞 A`. -/
theorem under_map_ringOfIntegersEquiv' {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] (e : A ≃+* B) (I : Ideal (NumberField.RingOfIntegers A)) :
    Ideal.under (NumberField.RingOfIntegers ℚ)
        (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e) I) =
      Ideal.under (NumberField.RingOfIntegers ℚ) I := by
  have hcomp : ((NK.Reconstruct.ringOfIntegersEquiv e :
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
  refine Ideal.ext (fun z => ?_)
  rw [Ideal.mem_comap, Ideal.mem_comap, ← hcomp, RingHom.comp_apply]
  exact Ideal.apply_mem_of_equiv_iff

/-- **The rational prime below a transported prime.** -/
theorem primeBelowNat_primeTransport' {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] (e : A ≃+* B) (P : NK.Chebotarev.PrimeIdeal A) :
    NK.LocalInputs.primeBelowNat B (NK.Reconstruct.primeTransport e P) =
      NK.LocalInputs.primeBelowNat A P := by
  have h : NK.LocalInputs.primeBelow B (NK.Reconstruct.primeTransport e P) =
      NK.LocalInputs.primeBelow A P := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    show Ideal.under (NumberField.RingOfIntegers ℚ)
        (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e) P.asIdeal) =
      Ideal.under (NumberField.RingOfIntegers ℚ) P.asIdeal
    exact under_map_ringOfIntegersEquiv' e P.asIdeal
  simp only [NK.LocalInputs.primeBelowNat]
  rw [h]

/-- The rational prime below a prime of a number field, as an equality test: `primeBelowNat`
determines `primeBelow`. -/
theorem primeBelow_eq_of_primeBelowNat_eq {L : Type*} [Field L] [NumberField L]
    {p q : NK.Chebotarev.PrimeIdeal L}
    (h : NK.LocalInputs.primeBelowNat L p = NK.LocalInputs.primeBelowNat L q) :
    NK.LocalInputs.primeBelow L p = NK.LocalInputs.primeBelow L q := by
  have h1 : Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow L p) =
      Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow L q) := Subtype.ext h
  exact Rat.HeightOneSpectrum.primesEquiv.injective h1

/-- For a prime `ℓ`, the map `n ↦ ℓ ^ n` is injective. -/
theorem pow_eq_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) {m k : ℕ} (h : ℓ ^ m = ℓ ^ k) : m = k := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd h (Nat.ne_of_lt (Nat.pow_lt_pow_right hℓ.one_lt hlt))
  · exact absurd h.symm (Nat.ne_of_lt (Nat.pow_lt_pow_right hℓ.one_lt hlt))

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- Finite-set form of the Kummer-theoretic prime identification (Uchida/Shimizu, arXiv:2601.01251
`lem:alpha identifies with sigma on primes`, restricted to a finite set of primes).

Given the levelwise weak Neukirch–Uchida input `hlev` (an isomorphism `↥L ≃+* ↥(levelMap ϕ L)` for
every finite level, no compatibility), a prime `ℓ` with `μ_ℓ ⊆ K₁`, a finite Galois level `L` whose
image level is Galois over `ℚ`, and a finite set `S` of primes of `𝓞 L`, there is a single level
isomorphism `τ : ↥L ≃+* ↥(levelMap ϕ L)` whose induced prime map agrees with the prime
correspondence `levelPrimeMap ϕ hϕ a L` on `S`.

Intended proof (the differentiation argument, exactly as in the sister file
`Submission/Work/ReconstructField/key_finite_prime_match.lean`): enlarge `S` to the finite set `S*` of
all primes of `L` over the finitely many rational primes below `S`; by
`NK.UchidaKummer.isDifferentiable_of_exists_isPrimitiveRoot` (base field `↥L`, from `hμ` and
`hℓ`) build a finite level `M ⊇ L` inside `K₁'` whose local degree over `L` is a distinct power
`ℓ ^ a_P` at every `P ∈ S*`; take the isomorphism `τ_M : M ≃+* levelMap ϕ M` given by `hlev`;
show `τ_M(L) = levelMap ϕ L` from the hypothesis `[IsGalois ℚ ↥(levelMap ϕ L)]` together with
`NK.ReconstructField.eq_of_isNormal_of_algEquiv` (both `τ_M(L)` and `levelMap ϕ L` are `ℚ`-embedded
subfields of `K₂'`, and `levelMap ϕ L` is normal over `ℚ`); then, for `P ∈ S`, the pullback
`τ_M⁻¹(levelPrimeMap L P)` of the base prime has the same residue characteristic as `P`
(`a.residueChar`), hence lies in `S*`, and its local degree over `L` equals `ℓ ^ a_P` by transport
along `τ_M` and the preservation of local degrees under `levelPrimeMap`; since the `a_Q` are
distinct this forces `τ_M⁻¹(levelPrimeMap L P) = P`, i.e. `τ_M(P) = levelPrimeMap L P`; restrict to
`L`. -/
theorem keyFinitePrimeMatch {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
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
  -- ## A primitive `ℓ`-th root of unity in `L`, and the differentiation lemma over `↥L`
  obtain ⟨ζ₀, hζ₀⟩ := hμ
  have hμL : ∃ ζ : ↥L, IsPrimitiveRoot ζ ℓ :=
    ⟨algebraMap K₁ ↥L ζ₀, hζ₀.map_of_injective (algebraMap K₁ ↥L).injective⟩
  haveI hSepL : IsSepClosure ↥L K₁' := isSepClosure_level L
  have hdiff : NK.UchidaKummer.IsDifferentiable ↥L K₁' ℓ :=
    NK.UchidaKummer.isDifferentiable_of_exists_isPrimitiveRoot (K := ↥L) (K' := K₁') ℓ hℓ hμL
  -- ## The finite set `S*` of primes of `L` over the rational primes below the primes of `S`
  set Sstar : Finset (NK.Chebotarev.PrimeIdeal ↥L) :=
    (S.image (fun Q => NK.LocalInputs.primeBelow ↥L Q)).biUnion (fun p =>
      NK.UchidaKummer.Differentiation.primesOverFinset (K := ℚ) (L := ↥L) p) with hSstar
  have mem_Sstar : ∀ Q : NK.Chebotarev.PrimeIdeal ↥L,
      Q ∈ Sstar ↔ ∃ P ∈ S, NK.LocalInputs.primeBelow ↥L Q =
        NK.LocalInputs.primeBelow ↥L P := by
    intro Q
    rw [hSstar, Finset.mem_biUnion]
    constructor
    · rintro ⟨p, hp, hQp⟩
      rw [Finset.mem_image] at hp
      obtain ⟨P, hPS, rfl⟩ := hp
      rw [NK.UchidaKummer.Differentiation.mem_primesOverFinset] at hQp
      exact ⟨P, hPS, NK.LocalInputs.ResidueChar.primeBelow_eq_of_liesOver Q (NK.LocalInputs.primeBelow ↥L P) hQp⟩
    · rintro ⟨P, hPS, hQ⟩
      refine ⟨NK.LocalInputs.primeBelow ↥L P, Finset.mem_image.mpr ⟨P, hPS, rfl⟩, ?_⟩
      rw [NK.UchidaKummer.Differentiation.mem_primesOverFinset, ← hQ]
      exact NK.LocalInputs.primeBelow_liesOver ↥L Q
  -- ## An enumeration of `S*` and distinct exponents
  letI : Fintype ↥Sstar := Finset.fintypeCoeSort Sstar
  let ee : ↥Sstar ≃ Fin (Fintype.card ↥Sstar) := Fintype.equivFin ↥Sstar
  let 𝔭 : Fin (Fintype.card ↥Sstar) → NK.Chebotarev.PrimeIdeal ↥L := fun i => (ee.symm i).1
  have h𝔭inj : Function.Injective 𝔭 := by
    intro i j hij
    exact ee.symm.injective (Subtype.ext hij)
  have h𝔭_spec : ∀ Q : ↥Sstar, 𝔭 (ee Q) = Q.1 :=
    fun Q => congrArg Subtype.val (Equiv.symm_apply_apply ee Q)
  -- ## The level `M'` over `↥L` produced by the differentiation lemma
  obtain ⟨M', hM'fin, hM'NF, hM'deg⟩ :=
    hdiff (Fintype.card ↥Sstar) 𝔭 h𝔭inj (fun i => (i : ℕ))
  -- ## The same level, presented over `K₁`
  set M : IntermediateField K₁ K₁' := toKi L M' with hMdef
  have hLM : L ≤ M := le_toKi L M'
  haveI hMfin : FiniteDimensional K₁ M := by
    haveI : FiniteDimensional K₁ ↥M' := FiniteDimensional.trans K₁ ↥L ↥M'
    exact inferInstanceAs (FiniteDimensional K₁ ↥M')
  haveI hMNF : NumberField ↥M := inferInstanceAs (NumberField ↥M')
  letI hAlg : Algebra ↥L ↥M := algOfLe L M hLM
  have hincl : ∀ x : ↥L, @algebraMap ↥L ↥M _ _ hAlg x = (⟨(x : K₁'), hLM x.2⟩ : ↥M) :=
    fun x => rfl
  haveI hST : IsScalarTower K₁ ↥L ↥M := isScalarTower_algOfLe L M hLM hincl
  -- the differentiation statement, transported to the `K₁`-presentation
  have hdeg : ∀ (i : Fin (Fintype.card ↥Sstar)) (Q : NK.Chebotarev.PrimeIdeal ↥M),
      Q.asIdeal.LiesOver (𝔭 i).asIdeal →
        NK.UchidaKummer.localDeg Q (𝔭 i) = ℓ ^ (i : ℕ) := by
    intro i Q hQ
    exact hM'deg i Q hQ
  -- ## The isomorphism of the large level, and its restriction to `L`
  let σ : ↥M ≃+* ↥(NK.Reconstruct.levelMap ϕ M) := Classical.choice (hlev M)
  haveI hLM'fin : FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ M) :=
    finiteDimensional_levelMap hϕ M
  have hexists := NK.ReconstructField.exists_levelIso_restrict (ϕ := ϕ) (hϕ := hϕ) (L := L) (M := M) hLM (hlev L) σ
  let τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L) := hexists.choose
  have hτ : ∀ x : ↥L, (τ x : K₂') = σ ⟨(x : K₁'), hLM x.2⟩ := hexists.choose_spec
  -- ## Instances for the corresponding level
  have hmono : NK.Reconstruct.levelMap ϕ L ≤ NK.Reconstruct.levelMap ϕ M :=
    NK.Reconstruct.levelMap_mono ϕ hLM
  letI hAlg₂ : Algebra ↥(NK.Reconstruct.levelMap ϕ L) ↥(NK.Reconstruct.levelMap ϕ M) :=
    algOfLe _ _ hmono
  have hincl₂ : ∀ y : ↥(NK.Reconstruct.levelMap ϕ L),
      @algebraMap _ _ _ _ hAlg₂ y = (⟨(y : K₂'), hmono y.2⟩ : ↥(NK.Reconstruct.levelMap ϕ M)) :=
    fun y => rfl
  haveI hST₂ : IsScalarTower K₂ ↥(NK.Reconstruct.levelMap ϕ L) ↥(NK.Reconstruct.levelMap ϕ M) :=
    isScalarTower_algOfLe _ _ hmono hincl₂
  haveI hNF' : NumberField ↥(NK.Reconstruct.levelMap ϕ M) :=
    NK.Reconstruct.numberField_levelMap hϕ M
  -- ## The two count identities
  have hcount₁ : ∀ P : NK.Chebotarev.PrimeIdeal ↥L,
      (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard =
        ((NK.ReconstructField.levelPrimeMap ϕ hϕ a L P).asIdeal.primesOver
          (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ M))).ncard :=
    fun P => NK.ReconstructField.ncard_primesOver_levelPrimeMapGen ϕ hϕ a L M hLM hincl hincl₂ P
  have hσcompat : ∀ x : ↥L, σ (@algebraMap ↥L ↥M _ _ hAlg x) =
      @algebraMap ↥(NK.Reconstruct.levelMap ϕ L) ↥(NK.Reconstruct.levelMap ϕ M) _ _ hAlg₂
        (τ x) := by
    intro x
    have h2 : ((@algebraMap _ _ _ _ hAlg₂ (τ x) :
        ↥(NK.Reconstruct.levelMap ϕ M)) : K₂') =
        ((τ x : ↥(NK.Reconstruct.levelMap ϕ L)) : K₂') := rfl
    apply Subtype.ext
    rw [show (@algebraMap ↥L ↥M _ _ hAlg x) = (⟨(x : K₁'), hLM x.2⟩ : ↥M) from rfl]
    rw [h2]
    exact (hτ x).symm
  have hcount₂ : ∀ P : NK.Chebotarev.PrimeIdeal ↥L,
      (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard =
        ((NK.Reconstruct.primeTransport τ P).asIdeal.primesOver
          (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ M))).ncard :=
    fun P => NK.ReconstructField.ncard_primesOver_primeTransport σ τ hσcompat P
  have hcount_deg : ∀ (Q : NK.Chebotarev.PrimeIdeal ↥L) (hQ : Q ∈ Sstar),
      (Q.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard *
        ℓ ^ ((ee ⟨Q, hQ⟩ : Fin (Fintype.card ↥Sstar)) : ℕ) = Module.finrank ↥L ↥M := by
    intro Q hQ
    have hQs : 𝔭 (ee ⟨Q, hQ⟩) = Q := h𝔭_spec ⟨Q, hQ⟩
    have key : ∀ (Q' : NK.Chebotarev.PrimeIdeal ↥M),
        Q'.asIdeal.LiesOver (𝔭 (ee ⟨Q, hQ⟩)).asIdeal →
          NK.UchidaKummer.localDeg Q' (𝔭 (ee ⟨Q, hQ⟩)) =
            ℓ ^ ((ee ⟨Q, hQ⟩ : Fin (Fintype.card ↥Sstar)) : ℕ) :=
      fun Q' hQ' => hdeg (ee ⟨Q, hQ⟩) Q' hQ'
    have hmain := NK.ReconstructField.ncard_primesOver_mul_eq_finrank_of_forall_localDeg
      (𝔭 := 𝔭 (ee ⟨Q, hQ⟩))
      (d := ℓ ^ ((ee ⟨Q, hQ⟩ : Fin (Fintype.card ↥Sstar)) : ℕ)) key
    rw [hQs] at hmain
    exact hmain
  -- ## The fibre count is injective on `S*`
  have hcount_inj : ∀ Q ∈ Sstar, ∀ Q' ∈ Sstar,
      (Q.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard =
        (Q'.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard → Q = Q' := by
    intro Q hQ Q' hQ' hcard
    obtain ⟨Qfib, hQfib⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := ↥L) (L := ↥M) Q'
    have hne : 0 < (Q'.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard := by
      rw [Set.ncard_pos]
      exact ⟨Qfib.asIdeal, Qfib.isPrime, hQfib⟩
    have h1 : (Q'.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard *
        ℓ ^ ((ee ⟨Q, hQ⟩ : Fin (Fintype.card ↥Sstar)) : ℕ) = Module.finrank ↥L ↥M := by
      rw [← hcard]
      exact hcount_deg Q hQ
    have h5 : ℓ ^ ((ee ⟨Q, hQ⟩ : Fin (Fintype.card ↥Sstar)) : ℕ) =
        ℓ ^ ((ee ⟨Q', hQ'⟩ : Fin (Fintype.card ↥Sstar)) : ℕ) :=
      Nat.mul_left_cancel hne (h1.trans (hcount_deg Q' hQ').symm)
    have h7 : ((ee ⟨Q, hQ⟩ : Fin (Fintype.card ↥Sstar)) : ℕ) =
        ((ee ⟨Q', hQ'⟩ : Fin (Fintype.card ↥Sstar)) : ℕ) := pow_eq_of_prime hℓ h5
    exact congrArg Subtype.val (ee.injective (Fin.ext h7))
  -- ## The correction `Ψ` of the prime correspondence
  let Ψ : NK.Chebotarev.PrimeIdeal ↥L → NK.Chebotarev.PrimeIdeal ↥L := fun Q =>
    NK.Reconstruct.primeTransport (τ.symm) (NK.ReconstructField.levelPrimeMap ϕ hϕ a L Q)
  have hΨ_transport : ∀ Q : NK.Chebotarev.PrimeIdeal ↥L,
      NK.Reconstruct.primeTransport τ (Ψ Q) = NK.ReconstructField.levelPrimeMap ϕ hϕ a L Q := by
    intro Q
    have h1 : NK.Reconstruct.primeTransport τ
        (NK.Reconstruct.primeTransport τ.symm (NK.ReconstructField.levelPrimeMap ϕ hϕ a L Q)) =
        NK.Reconstruct.primeTransport (τ.symm.trans τ)
          (NK.ReconstructField.levelPrimeMap ϕ hϕ a L Q) :=
      (NK.ReconstructField.primeTransport_trans (e := τ.symm) (f := τ)
        (P := NK.ReconstructField.levelPrimeMap ϕ hϕ a L Q)).symm
    rw [show Ψ Q = NK.Reconstruct.primeTransport τ.symm
        (NK.ReconstructField.levelPrimeMap ϕ hϕ a L Q) from rfl, h1]
    have h2 : τ.symm.trans τ = RingEquiv.refl ↥(NK.Reconstruct.levelMap ϕ L) := by ext x; simp
    rw [h2, NK.ReconstructField.primeTransport_refl]
  refine ⟨τ, fun P hP => ?_⟩
  have hPmem : P ∈ Sstar := (mem_Sstar P).mpr ⟨P, hP, rfl⟩
  have hΨmem : Ψ P ∈ Sstar := by
    rw [mem_Sstar]
    refine ⟨P, hP, ?_⟩
    exact primeBelow_eq_of_primeBelowNat_eq
      ((primeBelowNat_primeTransport' τ.symm
          (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P)).trans
        (NK.ReconstructField.primeBelowNat_levelPrimeMap ϕ hϕ a L P))
  have hA : ((Ψ P).asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard =
      ((NK.ReconstructField.levelPrimeMap ϕ hϕ a L P).asIdeal.primesOver
        (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ M))).ncard := by
    rw [← hΨ_transport P]
    exact hcount₂ (Ψ P)
  have hcount_eq : ((Ψ P).asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard =
      (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard :=
    hA.trans (hcount₁ P).symm
  have hfix : Ψ P = P := hcount_inj (Ψ P) hΨmem P hPmem hcount_eq
  exact (congrArg (NK.Reconstruct.primeTransport τ) hfix).symm.trans (hΨ_transport P)

end NK.Reconstruct
