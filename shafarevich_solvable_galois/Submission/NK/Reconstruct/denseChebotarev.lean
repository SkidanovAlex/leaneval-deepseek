import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.Chebotarev.ArtinReciprocity
import Submission.NK.Reconstruct.Reconstruction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Čebotarev with the prime restricted to a set of full density

The Čebotarev input (c) of the reconstruction (`NK.Reconstruct.ChebotarevInput`) asks for a single
prime at which a prescribed element is a Frobenius element.  That is *not* the form in which
Čebotarev is available in practice: the density theorem gives the prime only inside a set of
Dirichlet density `1/[L:K]`, and it is the union of finitely many proper closed subgroups of a
compact group that a Frobenius element must avoid (Shimizu, Prop. 4f.3; Serre, *Abelian ℓ-adic
representations*, Ch. I §2.2, Cor. 2).

This file gives the density form and proves that it is enough:

* `NK.Reconstruct.HasFullDensity K R` — `R` is a set of primes of Dirichlet density `1`.
* `NK.Reconstruct.ChebotarevDensityInput K K'` — the Čebotarev density theorem: the primes whose
  Frobenius element is conjugate to a prescribed `τ` have Dirichlet density
  `|Cl(τ)|/|Gal(L/K)|` (in particular positive).  It is **proved** from Artin reciprocity by
  `NK.Reconstruct.chebotarevDensityInput_of_artinReciprocity`; the Čebotarev input (c) itself is
  the special case `NK.Reconstruct.chebotarevInput_of_chebotarevInputWithin_univ`.
* `NK.Reconstruct.exists_isFrobAtPrime_mem_of_hasFullDensity` — **the density step**: every set of
  primes of full density contains a prime at which a prescribed `τ` is a Frobenius element.  (The
  proof is the standard one: the set of primes whose Frobenius class is that of `τ` has positive
  density, so it cannot be contained in the complement of `R`, which has density `0`.)
* `NK.Reconstruct.ChebotarevInputWithin K K' R` — the Čebotarev input with the prime restricted
  to `R`; it is **proved** from the density input for every `R` of full density
  (`NK.Reconstruct.chebotarevInputWithin_of_hasFullDensity`).
* `NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence_within` and
  `NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence_of_density` — **the endgame of the
  reconstruction with the prime restricted to `R`**: the conclusion `∃ σ, Conjugates σ ϕ` follows
  from a candidate `σ`, the σ-based Frobenius correspondence and the restricted Čebotarev input.
  This is the sharpest form of the reconstruction proved in this area: the Čebotarev input (c) is
  weakened from "some prime" to "a prime in a prescribed set of full density".

Reference: J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, XII §12.2;
S. Shimizu, arXiv:2009.10431, §4 (Prop. 4f.3); J.-P. Serre, *Abelian ℓ-adic Representations and
Elliptic Curves*, Ch. I §2.2.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

open scoped Pointwise

/-- **A set of primes of full Dirichlet density**: its complement has Dirichlet density `0`. -/
def HasFullDensity (K : Type*) [Field K] [NumberField K]
    (R : Set (NK.Chebotarev.PrimeIdeal K)) : Prop :=
  NumberField.Set.HasDirichletDensity Rᶜ 0

/-- **The Čebotarev density input.**  For every finite Galois level `L/K` and every `τ : Gal(L/K)`,
the primes of `K` whose Frobenius element is conjugate to `τ` have Dirichlet density
`|Cl(τ)| / |Gal(L/K)|`.

This is exactly the output of Čebotarev's density theorem as produced from Artin reciprocity
(`NK.Chebotarev.hasDirichletDensity_frobClass_of_artinReciprocity`), see
`NK.Reconstruct.chebotarevDensityInput_of_artinReciprocity`. -/
def ChebotarevDensityInput (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] : Prop :=
  ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (τ : Gal(↥L/K)),
    NumberField.Set.HasDirichletDensity
      {p : NK.Chebotarev.PrimeIdeal K |
        IsConj (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) p) τ}
      ((Nat.card {x : Gal(↥L/K) // IsConj x τ} : ℝ) / (Nat.card (Gal(↥L/K)) : ℝ))

/-- **Artin reciprocity implies the Čebotarev density input.**  This is
`NK.Chebotarev.hasDirichletDensity_frobClass_of_artinReciprocity`, the density of the primes whose
Frobenius element lies in the conjugacy class of `τ`. -/
theorem chebotarevDensityInput_of_artinReciprocity {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K']
    (h : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
      [IsGalois K ↥L], NK.Chebotarev.ArtinReciprocityInput K ↥L) :
    ChebotarevDensityInput K K' := by
  intro L _ _ _ τ
  haveI hgal : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  exact NK.Chebotarev.hasDirichletDensity_frobClass_of_artinReciprocity (K := K) (L := ↥L)
    (h L) τ

/-- The density appearing in the Čebotarev density input is positive. -/
theorem chebotarevDensityInput_pos {K : Type*} [Field K] [NumberField K]
    {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [Normal K L]
    (τ : Gal(L/K)) :
    (0 : ℝ) < (Nat.card {x : Gal(L/K) // IsConj x τ} : ℝ) / (Nat.card (Gal(L/K)) : ℝ) := by
  haveI : Nonempty {x : Gal(L/K) // IsConj x τ} := ⟨τ, IsConj.refl τ⟩
  haveI : Nonempty (Gal(L/K)) := ⟨1⟩
  have h1 : (0 : ℝ) < (Nat.card {x : Gal(L/K) // IsConj x τ} : ℝ) := by
    exact_mod_cast Nat.card_pos
  have h2 : (0 : ℝ) < (Nat.card (Gal(L/K)) : ℝ) := by exact_mod_cast Nat.card_pos
  exact div_pos h1 h2

/-- **The Čebotarev density step.**  Every set of primes of full Dirichlet density contains a prime
at which a prescribed element `τ` of a finite Galois level is an arithmetic Frobenius element.

Proof: the set `S` of primes whose Frobenius element is conjugate to `τ` has positive density, so it
cannot be contained in the complement of `R` (which has density `0`).  At a prime of `S` the chosen
Frobenius representative is conjugate to `τ`, and conjugating the prime turns it into a genuine
Frobenius element at `τ` (`NK.Chebotarev.IsFrobAtConj`). -/
theorem exists_isFrobAtPrime_mem_of_hasFullDensity {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K']
    (hc : ChebotarevDensityInput K K') {R : Set (NK.Chebotarev.PrimeIdeal K)}
    (hR : HasFullDensity K R)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (τ : Gal(↥L/K)) :
    ∃ p ∈ R, NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥L) p τ := by
  classical
  haveI hgal : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  set S : Set (NK.Chebotarev.PrimeIdeal K) :=
    {p | IsConj (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) p) τ} with hSdef
  have hdens : NumberField.Set.HasDirichletDensity S
      ((Nat.card {x : Gal(↥L/K) // IsConj x τ} : ℝ) / (Nat.card (Gal(↥L/K)) : ℝ)) :=
    hc L τ
  have hδpos := chebotarevDensityInput_pos (K := K) (L := ↥L) τ
  by_contra hcon
  push_neg at hcon
  have hsub : S ⊆ Rᶜ := by
    intro p hp
    simp only [Set.mem_compl_iff]
    intro hpR
    -- the chosen Frobenius representative at `p` is a genuine Frobenius element
    obtain ⟨σ₀, hσ₀⟩ := NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := ↥L) p
    have hne : ∃ σ : Gal(↥L/K), NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥L) p σ :=
      ⟨σ₀, hσ₀⟩
    have hfrobp : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥L) p
        (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) p) := by
      rw [NK.Chebotarev.frobAtPrime, dif_pos hne]
      exact hne.choose_spec
    obtain ⟨P, hP, hFP⟩ := hfrobp
    obtain ⟨c, hc⟩ := isConj_iff.mp hp
    have hconj : NK.Chebotarev.IsFrobAt (c • P) τ := by
      have h := NK.Chebotarev.IsFrobAtConj (K := K) (L := ↥L) (τ := c) hFP
      rw [hc] at h
      exact h
    have hLies : (c • P).asIdeal.LiesOver p.asIdeal := by
      haveI : P.asIdeal.LiesOver p.asIdeal := hP
      rw [NK.Chebotarev.smul_primeIdeal_asIdeal]
      exact Commons.NumberTheory.NumberField.liesOver_map_galRestrict p P c
    exact hcon p hpR ⟨c • P, hLies, hconj⟩
  -- `S` would then have density `0`, contradicting its positive density
  have hzero : NumberField.Set.HasDirichletDensity S 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_subset hR hsub
  rw [NumberField.Set.HasDirichletDensity] at hdens hzero
  have h0 : (0 : ℝ) = (Nat.card {x : Gal(↥L/K) // IsConj x τ} : ℝ) /
      (Nat.card (Gal(↥L/K)) : ℝ) := tendsto_nhds_unique hzero hdens
  exact absurd h0.symm hδpos.ne'

/-- **The Čebotarev input with the prime restricted to a set `R`**: every element of every finite
Galois level is an arithmetic Frobenius element at an *unramified* prime belonging to `R`. -/
def ChebotarevInputWithin (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] (R : Set (NK.Chebotarev.PrimeIdeal K)) : Prop :=
  ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (τ : Gal(↥L/K)),
    ∃ p ∈ R, ∃ P : NK.Chebotarev.PrimeIdeal ↥L,
      P.asIdeal.LiesOver p.asIdeal ∧
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
      NK.Chebotarev.IsFrobAt P τ

/-- **The density input gives the restricted Čebotarev input at every set of full density.**
The only further point is that the primes of `K` ramifying in `L/K` form a *finite*, hence
density-zero, set, so they may be removed from `R` without changing the density. -/
theorem chebotarevInputWithin_of_hasFullDensity {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K']
    (hc : ChebotarevDensityInput K K') {R : Set (NK.Chebotarev.PrimeIdeal K)}
    (hR : HasFullDensity K R) : ChebotarevInputWithin K K' R := by
  classical
  intro L _ _ _ τ
  set Bad : Set (NK.Chebotarev.PrimeIdeal K) :=
    {p | ∃ P : NK.Chebotarev.PrimeIdeal ↥L,
      P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1} with hBaddef
  have hBadFin : Bad.Finite := by
    have hfin : {q : NK.Chebotarev.PrimeIdeal ↥L |
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}.Finite :=
      Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
    refine (hfin.image (fun q : NK.Chebotarev.PrimeIdeal ↥L =>
      IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) q)).subset ?_
    rintro p ⟨P, hP, heP⟩
    exact ⟨P, heP, IsDedekindDomain.HeightOneSpectrum.ext
      (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, hP.over])⟩
  have hBadZero : NumberField.Set.HasDirichletDensity Bad 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite hBadFin
  -- `R \ Bad` still has full density
  have hR' : HasFullDensity K (R \ Bad) := by
    have hcompl : (R \ Bad)ᶜ = Rᶜ ∪ Bad := by
      ext p
      simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union]
      tauto
    rw [HasFullDensity, hcompl]
    exact Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero hR hBadZero
  obtain ⟨p, hp, hfrob⟩ :=
    exists_isFrobAtPrime_mem_of_hasFullDensity (K := K) (K' := K') hc hR' L τ
  have hpR : p ∈ R := hp.1
  have hpBad : p ∉ Bad := hp.2
  obtain ⟨P, hP, hFP⟩ := hfrob
  refine ⟨p, hpR, P, hP, ?_, hFP⟩
  by_contra hne
  exact hpBad ⟨P, hP, hne⟩

/-- The unrestricted Čebotarev input is the special case `R = univ` of the restricted one. -/
theorem chebotarevInput_of_chebotarevInputWithin_univ {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K']
    (h : ChebotarevInputWithin K K' Set.univ) : ChebotarevInput K K' := by
  intro L _ _ _ τ
  obtain ⟨p, -, P, hP, he, hFP⟩ := h L τ
  exact ⟨p, P, hP, he, hFP⟩

section Endgame

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The Frobenius correspondence (b) restricted to the primes of `R`.**  This is
`NK.Reconstruct.FrobeniusCorrespondence` with the pair of primes restricted to a set `R`: at a
prime of `R`, the correspondence of Frobenius elements is required, and nothing is required at the
primes outside `R`.

It is the form in which the correspondence is available from the density input: Čebotarev produces
the primes only inside a set of full density, and the endgame of
`NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence_within_of_within` uses the correspondence
only at those primes. -/
def FrobeniusCorrespondenceWithin (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (σ : K₂' ≃+* K₁')
    (R : Set (NK.Chebotarev.PrimeIdeal K₁)) : Prop :=
  ∀ (L₂ : IntermediateField K₂ K₂') [FiniteDimensional K₂ L₂] [Normal K₂ L₂] [NumberField ↥L₂]
    (L₁ : IntermediateField K₁ K₁') [FiniteDimensional K₁ L₁] [Normal K₁ L₁] [NumberField ↥L₁]
    (τ : ↥L₁ ≃+* ↥L₂), (∀ x : ↥L₁, (τ x : K₂') = σ.symm (x : K₁')) →
    ∀ (p : NK.Chebotarev.PrimeIdeal K₁), p ∈ R → ∀ P : NK.Chebotarev.PrimeIdeal ↥L₁,
      P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K₁) = 1 →
      ∀ g : Gal(K₁'/K₁),
        NK.Chebotarev.IsFrobAt P (AlgEquiv.restrictNormalHom L₁ g) →
          NK.Chebotarev.IsFrobAt (primeTransport τ P)
            (AlgEquiv.restrictNormalHom L₂ (ϕ g))

/-- The unrestricted Frobenius correspondence implies the correspondence restricted to any `R`. -/
theorem frobeniusCorrespondenceWithin_of_frobeniusCorrespondence
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {σ : K₂' ≃+* K₁'}
    {R : Set (NK.Chebotarev.PrimeIdeal K₁)} (b : FrobeniusCorrespondence ϕ σ) :
    FrobeniusCorrespondenceWithin ϕ σ R := by
  intro L₂ _ _ _ L₁ _ _ _ τ hτ p _ P hP hunr g hg
  exact b L₂ L₁ τ hτ p P hP hunr g hg

/-- **The endgame of the reconstruction with the Čebotarev prime restricted to `R`.**

This is the sharpest form of the endgame of the reconstruction: *both* the Čebotarev input and
the Frobenius correspondence are relaxed to a set `R` of primes.  The Čebotarev input is weakened
from `ChebotarevInput K₁ K₁'` (an unramified prime, no condition) to
`ChebotarevInputWithin K₁ K₁' R` (an unramified prime inside `R`), and the Frobenius
correspondence from `FrobeniusCorrespondence ϕ σ` to `FrobeniusCorrespondenceWithin ϕ σ R`
(no condition on the primes outside `R`).  The proof is the same
level-by-level argument: at each finite normal level `L₂/K₂` the restricted Čebotarev input provides
a prime of `R` at which a prescribed automorphism is a Frobenius element, and the uniqueness of the
Frobenius at an unramified prime converts the Frobenius correspondence into the required conjugacy.

By `NK.Reconstruct.chebotarevInputWithin_of_hasFullDensity`, the hypothesis is available for every
`R` of full Dirichlet density. -/
theorem exists_sigma_of_frobeniusCorrespondence_within_of_within (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    {R : Set (NK.Chebotarev.PrimeIdeal K₁)} (b : FrobeniusCorrespondenceWithin ϕ σ R)
    (c : ChebotarevInputWithin K₁ K₁' R) :
    ∃ σ' : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ' ϕ := by
  refine ⟨σ, hσ, ?_⟩
  have key : ∀ (g : Gal(K₁'/K₁)) (L₂ : IntermediateField K₂ K₂') [FiniteDimensional K₂ L₂]
      [Normal K₂ L₂] [NumberField ↥L₂],
      AlgEquiv.restrictNormalHom L₂ (ϕ g) =
        AlgEquiv.restrictNormalHom L₂
          (Submission.NeukirchUchida.conjHomEquiv hσ g) := by
    intro g L₂ _ _ _
    let L₁ : IntermediateField K₁ K₁' := sigmaLevel σ hσ L₂
    haveI hL₁fd : FiniteDimensional K₁ L₁ :=
      finiteDimensional_sigmaLevel σ hσ L₂
    haveI hL₁n : Normal K₁ L₁ := normal_sigmaLevel σ hσ L₂
    haveI hL₁nf : NumberField ↥L₁ :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField L₁
    haveI hL₁gal : IsGalois K₁ ↥L₁ :=
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    let τ : ↥L₁ ≃+* ↥L₂ := sigmaLevelEquiv σ hσ L₂
    have hτ : MapsBaseLevel L₁ L₂ τ := mapsBaseLevel_sigmaLevelEquiv σ hσ L₂
    have hσ' : ∀ x : ↥L₁, (τ x : K₂') = σ.symm (x : K₁') := fun x =>
      sigmaLevelEquiv_apply σ hσ L₂ x
    obtain ⟨p, hp, P, hP, he, hfrob⟩ := c L₁ (AlgEquiv.restrictNormalHom L₁ g)
    have h1 : NK.Chebotarev.IsFrobAt (primeTransport τ P)
        (AlgEquiv.restrictNormalHom L₂ (ϕ g)) := b L₂ L₁ τ hσ' p hp P hP he g hfrob
    have h2 : NK.Chebotarev.IsFrobAt P
        (conjAlgEquiv τ.symm hτ.symm (AlgEquiv.restrictNormalHom L₂ (ϕ g))) :=
      (isFrobAt_primeTransport_iff_inv hτ (AlgEquiv.restrictNormalHom L₂ (ϕ g)) P).mp h1
    have h3 : conjAlgEquiv τ.symm hτ.symm (AlgEquiv.restrictNormalHom L₂ (ϕ g)) =
        AlgEquiv.restrictNormalHom L₁ g :=
      NK.Chebotarev.IsFrobAt.eq_of_isFrobAt hP he h2 hfrob
    have h4 : AlgEquiv.restrictNormalHom L₂
          (Submission.NeukirchUchida.conjHomEquiv hσ g) =
        conjAlgEquiv τ hτ (AlgEquiv.restrictNormalHom L₁ g) :=
      restrictNormalHom_conjHomEquiv σ hσ L₂ g
    rw [h4]
    have h5 : conjAlgEquiv τ hτ
        (conjAlgEquiv τ.symm hτ.symm (AlgEquiv.restrictNormalHom L₂ (ϕ g))) =
        conjAlgEquiv τ hτ (AlgEquiv.restrictNormalHom L₁ g) := by rw [h3]
    rwa [conjAlgEquiv_conjAlgEquiv_symm] at h5
  have hgal : IsGalois K₂ K₂' := IsSepClosure.isGalois
  intro g
  have heq : ϕ = Submission.NeukirchUchida.conjHomEquiv hσ :=
    MulEquiv.ext fun g =>
      @eq_of_restrictNormalHom_eq K₂ K₂' _ _ _ _ hgal (ϕ g)
        (Submission.NeukirchUchida.conjHomEquiv hσ g) (key g)
  have h1 : (ϕ g : K₂' ≃+* K₂') =
      ((Submission.NeukirchUchida.conjHomEquiv hσ g : Gal(K₂'/K₂)) : K₂' ≃+* K₂') :=
    congrArg (fun e : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂) =>
      ((e g : Gal(K₂'/K₂)) : K₂' ≃+* K₂')) heq
  exact h1.trans (Submission.NeukirchUchida.conj_toRingEquiv hσ g)

/-- **The endgame of the reconstruction with the Čebotarev prime restricted to `R`.**

This is `NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence` with the Čebotarev input
weakened from `ChebotarevInput K₁ K₁'` (an unramified prime, no condition) to
`ChebotarevInputWithin K₁ K₁' R` (an unramified prime inside `R`).  The proof is the same
level-by-level argument: at each finite normal level `L₂/K₂` the restricted Čebotarev input provides
a prime of `R` at which a prescribed automorphism is a Frobenius element, and the uniqueness of the
Frobenius at an unramified prime converts the Frobenius correspondence into the required conjugacy.

By `NK.Reconstruct.chebotarevInputWithin_of_hasFullDensity`, the hypothesis is available for every
`R` of full Dirichlet density. -/
theorem exists_sigma_of_frobeniusCorrespondence_within (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (b : FrobeniusCorrespondence ϕ σ) {R : Set (NK.Chebotarev.PrimeIdeal K₁)}
    (c : ChebotarevInputWithin K₁ K₁' R) :
    ∃ σ' : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ' ϕ := by
  refine ⟨σ, hσ, ?_⟩
  have key : ∀ (g : Gal(K₁'/K₁)) (L₂ : IntermediateField K₂ K₂') [FiniteDimensional K₂ L₂]
      [Normal K₂ L₂] [NumberField ↥L₂],
      AlgEquiv.restrictNormalHom L₂ (ϕ g) =
        AlgEquiv.restrictNormalHom L₂
          (Submission.NeukirchUchida.conjHomEquiv hσ g) := by
    intro g L₂ _ _ _
    let L₁ : IntermediateField K₁ K₁' := sigmaLevel σ hσ L₂
    haveI hL₁fd : FiniteDimensional K₁ L₁ :=
      finiteDimensional_sigmaLevel σ hσ L₂
    haveI hL₁n : Normal K₁ L₁ := normal_sigmaLevel σ hσ L₂
    haveI hL₁nf : NumberField ↥L₁ :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField L₁
    haveI hL₁gal : IsGalois K₁ ↥L₁ :=
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    let τ : ↥L₁ ≃+* ↥L₂ := sigmaLevelEquiv σ hσ L₂
    have hτ : MapsBaseLevel L₁ L₂ τ := mapsBaseLevel_sigmaLevelEquiv σ hσ L₂
    have hσ' : ∀ x : ↥L₁, (τ x : K₂') = σ.symm (x : K₁') := fun x =>
      sigmaLevelEquiv_apply σ hσ L₂ x
    obtain ⟨p, -, P, hP, he, hfrob⟩ := c L₁ (AlgEquiv.restrictNormalHom L₁ g)
    have h1 : NK.Chebotarev.IsFrobAt (primeTransport τ P)
        (AlgEquiv.restrictNormalHom L₂ (ϕ g)) := b L₂ L₁ τ hσ' p P hP he g hfrob
    have h2 : NK.Chebotarev.IsFrobAt P
        (conjAlgEquiv τ.symm hτ.symm (AlgEquiv.restrictNormalHom L₂ (ϕ g))) :=
      (isFrobAt_primeTransport_iff_inv hτ (AlgEquiv.restrictNormalHom L₂ (ϕ g)) P).mp h1
    have h3 : conjAlgEquiv τ.symm hτ.symm (AlgEquiv.restrictNormalHom L₂ (ϕ g)) =
        AlgEquiv.restrictNormalHom L₁ g :=
      NK.Chebotarev.IsFrobAt.eq_of_isFrobAt hP he h2 hfrob
    have h4 : AlgEquiv.restrictNormalHom L₂
          (Submission.NeukirchUchida.conjHomEquiv hσ g) =
        conjAlgEquiv τ hτ (AlgEquiv.restrictNormalHom L₁ g) :=
      restrictNormalHom_conjHomEquiv σ hσ L₂ g
    rw [h4]
    have h5 : conjAlgEquiv τ hτ
        (conjAlgEquiv τ.symm hτ.symm (AlgEquiv.restrictNormalHom L₂ (ϕ g))) =
        conjAlgEquiv τ hτ (AlgEquiv.restrictNormalHom L₁ g) := by rw [h3]
    rwa [conjAlgEquiv_conjAlgEquiv_symm] at h5
  have hgal : IsGalois K₂ K₂' := IsSepClosure.isGalois
  intro g
  have heq : ϕ = Submission.NeukirchUchida.conjHomEquiv hσ :=
    MulEquiv.ext fun g =>
      @eq_of_restrictNormalHom_eq K₂ K₂' _ _ _ _ hgal (ϕ g)
        (Submission.NeukirchUchida.conjHomEquiv hσ g) (key g)
  have h1 : (ϕ g : K₂' ≃+* K₂') =
      ((Submission.NeukirchUchida.conjHomEquiv hσ g : Gal(K₂'/K₂)) : K₂' ≃+* K₂') :=
    congrArg (fun e : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂) =>
      ((e g : Gal(K₂'/K₂)) : K₂' ≃+* K₂')) heq
  exact h1.trans (Submission.NeukirchUchida.conj_toRingEquiv hσ g)

/-- **The reconstruction from the density form of Čebotarev.**  For any candidate `σ` realizing `ϕ`
through the Frobenius correspondence, and any set `R` of primes of full Dirichlet density, the
density form of Čebotarev (a consequence of Artin reciprocity) already forces `ϕ` to be the
conjugation by `σ`. -/
theorem exists_sigma_of_frobeniusCorrespondence_of_density (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (b : FrobeniusCorrespondence ϕ σ) (hc : ChebotarevDensityInput K₁ K₁')
    {R : Set (NK.Chebotarev.PrimeIdeal K₁)} (hR : HasFullDensity K₁ R) :
    ∃ σ' : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ' ϕ :=
  exists_sigma_of_frobeniusCorrespondence_within ϕ σ hσ b
    (chebotarevInputWithin_of_hasFullDensity (K := K₁) (K' := K₁') hc hR)

end Endgame

end NK.Reconstruct
