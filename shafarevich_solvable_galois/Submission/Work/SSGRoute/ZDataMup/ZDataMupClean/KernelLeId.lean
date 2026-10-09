import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
import Submission.Work.SSGRoute.ZDataMup.ZDataMupClean.CellId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.transfer.fracCoprimeId_relNormUnit
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.transfer.normRayId_map_relNormUnit_le
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.transfer.pow_finrank_mem_normRayId
import Submission.Work.SSGRoute.ZDataMup.MupAux.AuxId
import Submission.Work.SSGRoute.ZDataMup.MupAux.Base
import Submission.Work.SSGRoute.ZDataMup.MupAux.DescentId
import Submission.Work.SSGRoute.ZDataMup.MupAux.LImageId
import Submission.Work.SSGRoute.ZDataMup.MupAux.RestrictArtinId
import Submission.Work.SSGRoute.ZDataMup.MupAux.RestrictId
import Submission.Work.SSGRoute.ZDataMup.MupAux.TransportId
import Submission.NK.NUV2.ARL.transferSelfContained
import Submission.NK.CFTLib.ARLAlt.Setup
import Submission.NK.CFTLib.ARLAlt.CellAtAux
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.NK.CFTLib.ARL.RelNormFI
import Submission.NK.CFTLib.ArtinReciprocityIdeal.relNormUnit_trans
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.NK.GlobalCFTdeep.secondInequality_unconditional
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lang's conductor theorem for an ideal modulus: the transfer

`Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.kernelLeId_clean` is the ideal-modulus form of
Lang, *Algebraic Number Theory*, Ch. X §2, Theorem 2 (Childress, *Class Field Theory*, Prop. 2.2):
for a finite **cyclic** extension `L/K` of number fields and an ideal modulus `𝔪 ≠ ⊥` which is
admissible and contains all the primes ramified in `L/K`, every fractional ideal `A` of `K` coprime
to `𝔪` whose Artin symbol is trivial lies in `P(𝔪)·𝔑(𝔪)`.

The proof is the transfer argument, transported from the natural-number-modulus version
`NK.NUV2.ARL.SC.kernelLeOfAuxFieldSC`:

* `MupAux.AuxFieldHypId` / `MupAux.auxFieldHypId` — Artin's lemma at an ideal modulus;
* `cyclotomicCellKernelLeId_clean` (this lane, `cellId.lean`) — the cyclotomic cell at an ideal modulus;
* `MupAux.principalRayId_map_relNormUnit_le`, `transfer.normRayId_map_relNormUnit_le` — the two
  descents along the relative norm;
* `MupAux.spanUnit_norm_mem_principalRayId_of_congrOneId`, `MupAux.artinSymId_algEquiv`,
  `MupAux.artinSymId_restrict_relNorm`, `MupAux.restrictNormalHom_artinSymId_eq_ofLe`,
  `MupAux.normRayId_LImage_eq`, `MupAux.isUnramified_LImageId`,
  `MupAux.isUnramified_iff_ramificationIdxIn_eq_one_Id` — the transport and bookkeeping lemmas.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

open NK.CFTLib.ArtinReciprocityIdeal

open Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.transfer

/-- `Ideal.map` of the span of a natural number is the span of that natural number. -/
private lemma map_span_natCast {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) : Ideal.map (algebraMap A B) (Ideal.span {(n : A)}) = Ideal.span {(n : B)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- `𝔭` divides a product `𝔪·(M)` iff it divides `𝔪` or contains `M`. -/
private lemma dvdPrime_mul_span_iff {k : Type*} [Field k] [NumberField k]
    {𝔞 : Ideal (𝓞 k)} {M : ℕ} {𝔭 : HeightOneSpectrum (𝓞 k)} :
    DvdPrime (𝔞 * Ideal.span {(M : 𝓞 k)}) 𝔭 ↔
      DvdPrime 𝔞 𝔭 ∨ (M : 𝓞 k) ∈ 𝔭.asIdeal := by
  exact (Ideal.IsPrime.mul_le 𝔭.isPrime).trans
    (or_congr Iff.rfl (Ideal.span_singleton_le_iff_mem 𝔭.asIdeal))


/-- **Descent of the norm ray from the cyclotomic cell.**  The relative norm `N_{E/K}` maps the
norm ray of the cell `E·L/E` into the norm ray of `L/K` (ideal-modulus form of
`NK.NUV2.ARL.SC.normRay_cell_descent`). -/
private theorem normRayId_cell_descent {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M] (E : IntermediateField K (CyclotomicField M L))
    [FiniteDimensional ↥E ↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)]
    [FiniteDimensional K ↥E] [NumberField ↥E]
    (𝔠 : Ideal (𝓞 ↥E)) (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥)
    (hcm : 𝔠 ≤ Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔪) :
    (NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := ↥E)
        (L := ↥(NK.CFTLib.ARLAlt.ofLe E
          (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)) 𝔠).map
        (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E))
      ≤ NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
  letI : Algebra ↥E ↥(NK.CFTLib.ARLAlt.ofLe
      (NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_right) :=
    inferInstanceAs (Algebra ↥E ↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left))
  letI : IsScalarTower K ↥E ↥(NK.CFTLib.ARLAlt.ofLe
      (NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_right) :=
    inferInstanceAs (IsScalarTower K ↥E ↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left))
  have h := normRayId_map_relNormUnit_le (K := K)
    (L := ↥(NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)) (E := ↥E)
    (LE := ↥(NK.CFTLib.ARLAlt.ofLe (NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_right)) 𝔠 𝔪 h𝔪 hcm
  refine le_trans (le_of_eq ?_) (le_trans h ?_)
  · rfl
  · rw [Work.SSGRoute.ZDataMup.MupAux.normRayId_LImage_eq (K := K) (L := L) M 𝔪]

theorem kernelLeId_clean
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissibleId (K := K) (L := L) 𝔪)
    (hram : NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪 A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
  classical
  intro A hcop hsym
  haveI hMC : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨hcomm⟩⟩
  set Afr : FractionalIdeal (𝓞 K)⁰ K := (A : FractionalIdeal (𝓞 K)⁰ K) with hAfrdef
  set s : Finset (NK.Chebotarev.PrimeIdeal K) := (NK.CFTLib.Arl.exps Afr).support with hsdef
  have hfac : A = ∏ 𝔭 ∈ s, (NK.CFTLib.ARL.primeUnit 𝔭) ^ (NK.CFTLib.Arl.exps Afr) 𝔭 := by
    rw [hsdef]; exact NK.NUV2.ARL.SC.frac_eq_prod_primeUnit A
  have hs : ∀ 𝔭 ∈ s, ¬ NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 := by
    intro 𝔭 h𝔭 hmem
    exact (Finsupp.mem_support_iff.mp (hsdef ▸ h𝔭)) (by
      rw [NK.CFTLib.Arl.exps_apply]; exact hcop 𝔭 hmem)
  rcases s.eq_empty_or_nonempty with hsemp | hsne
  · rw [hfac, hsemp, Finset.prod_empty]; exact Subgroup.one_mem _
  obtain ⟨𝔭₀, h𝔭₀⟩ := hsne
  -- ## the auxiliary data
  obtain ⟨M, hMne, hM𝔪, _hMS, hMN, _hdisjζ, E, hEdisj, hE𝔭⟩ :=
    Work.SSGRoute.ZDataMup.MupAux.auxFieldHypId (K := K) (L := L) 𝔪 h𝔪 s hs ∅ (by simp)
  haveI : NeZero M := hMne
  set LΩ : IntermediateField K (CyclotomicField M L) :=
    NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M with hLΩdef
  set ζ : CyclotomicField M L := IsCyclotomicExtension.zeta M L (CyclotomicField M L) with hζdef
  -- the moduli: `𝔪` is the target modulus, `𝔫K = 𝔪·(M)` the "cell" modulus over `K`
  set 𝔫K : Ideal (𝓞 K) := 𝔪 * Ideal.span {(M : 𝓞 K)} with h𝔫Kdef
  have hM0 : (M : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have h𝔫Kne : 𝔫K ≠ ⊥ := by
    rw [h𝔫Kdef]
    intro h
    rcases (Ideal.mul_eq_bot.mp h) with h1 | h1
    · exact h𝔪 h1
    · exact hM0 (Ideal.span_singleton_eq_bot.mp h1)
  -- ## the auxiliary fields `E𝔭`
  have hE' : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      ∃ E𝔭 : IntermediateField K (CyclotomicField M L),
        E𝔭 ≤ E ∧ ((E𝔭.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
          ({ζ} : Set (CyclotomicField M L))) = ⊤) ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥E𝔭) 𝔭.1 1 :=
    fun 𝔭 => hE𝔭 𝔭.1 𝔭.2
  choose Ef hEfle hEfjoin hEfsplit using hE'
  have hsupE : (E.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
      ({ζ} : Set (CyclotomicField M L))) = ⊤ := by
    rw [eq_top_iff]
    refine le_trans (le_of_eq (hEfjoin ⟨𝔭₀, h𝔭₀⟩).symm) ?_
    exact sup_le_sup_right (fun x hx => hEfle ⟨𝔭₀, h𝔭₀⟩ hx) _
  haveI hcycE : IsCyclotomicExtension {M} ↥E (CyclotomicField M L) :=
    NK.CFTLib.ARLAlt.isCyclotomicExtension_of_sup_adjoin_zeta (K := K) (L := L) M E hsupE
  haveI habelE : IsAbelianGalois ↥E (CyclotomicField M L) :=
    IsCyclotomicExtension.isAbelianGalois {M} ↥E (CyclotomicField M L)
  haveI hcommCycE : IsMulCommutative (Gal(CyclotomicField M L/↥E)) :=
    habelE.toIsMulCommutative
  haveI hgalΩ : IsGalois K (CyclotomicField M L) :=
    NK.CFTLib.ARL.isGalois_cyclotomicField_over_base (K := K) (L := L) M
  -- ## `LΩ` and its Galois theory
  haveI hcommΩ : IsMulCommutative (Gal(↥LΩ/K)) :=
    NK.NUV2.ARL.SC.isMulCommutative_LImage (K := K) (L := L) M
  have hcommΩ' : ∀ a b : Gal(↥LΩ/K), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  haveI hnfE : NumberField ↥E :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField E
  haveI hnfLΩ : NumberField ↥LΩ :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField LΩ
  -- the moduli over `↥E` and over the auxiliary fields `E𝔭`
  have h𝔫Ene : (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔫K) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot h𝔫Kne
  -- ## ramification
  have hramE : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
      Ideal.ramificationIdxIn 𝔮.asIdeal (𝓞 (CyclotomicField M L)) ≠ 1 →
      DvdPrime (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔫K) 𝔮 := by
    intro 𝔮 h𝔮
    have hM𝔮 : (M : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
      by_contra hM
      exact h𝔮 ((isUnramified_iff_ramificationIdxIn_eq_one_Id (K := ↥E)
        (L := CyclotomicField M L) 𝔮).mp
        (NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := ↥E)
          (Ω := CyclotomicField M L) M 𝔮 hM))
    calc Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔫K
        = Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔪 * Ideal.span {(M : 𝓞 ↥E)} := by
          rw [h𝔫Kdef, Ideal.map_mul, map_span_natCast]
      _ ≤ Ideal.span {(M : 𝓞 ↥E)} := Ideal.mul_le_right
      _ ≤ 𝔮.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hM𝔮
  have hramL : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      DvdPrime 𝔫K p := by
    intro p hp
    have hp' : p.asIdeal.ramificationIdxIn (𝓞 L) ≠ 1 := fun h =>
      hp ((isUnramified_iff_ramificationIdxIn_eq_one_Id (K := K) (L := L) p).mpr h)
    exact le_trans (by rw [h𝔫Kdef]; exact Ideal.mul_le_left) (hram p hp')
  have hramLΩ : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥LΩ) p →
      DvdPrime 𝔫K p := by
    intro p hp
    have h2 : NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 p ∨ (M : 𝓞 K) ∈ p.asIdeal := by
      by_contra hc
      push_neg at hc
      exact hp (Work.SSGRoute.ZDataMup.MupAux.isUnramified_LImageId (K := K) (L := L)
        M 𝔪 hram p hc.1 hc.2)
    rcases h2 with h | h
    · exact le_trans (by rw [h𝔫Kdef]; exact Ideal.mul_le_left) h
    · exact le_trans (by rw [h𝔫Kdef]; exact Ideal.mul_le_right)
        ((Ideal.span_singleton_le_iff_mem _).mpr h)
  -- ## `A` is coprime to `𝔫K`
  have hMnotmem : ∀ 𝔭 ∈ s, (M : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭 hmem
    obtain ⟨p, hp, hpM, hpN⟩ := NK.NUV2.ARL.SC.exists_prime_dvd_absNorm_of_mem (K := K) hmem
    exact hMN p hp hpM 𝔭 h𝔭 hpN
  have hcop𝔫 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔫K A := by
    intro 𝔭 hmem
    rw [h𝔫Kdef] at hmem
    rcases (Ideal.IsPrime.mul_le 𝔭.isPrime).mp hmem with h | h
    · exact hcop 𝔭 h
    · by_contra hne
      exact hMnotmem 𝔭 (hsdef.symm ▸ Finsupp.mem_support_iff.mpr hne)
        ((Ideal.span_singleton_le_iff_mem _).mp h)
  -- ## the transport to `LΩ`
  have hsym' : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm Afr = 1 := hsym
  have hsymΩ : NK.CFTLib.Arl.artinSym (K := K) (L := ↥LΩ) hcommΩ' Afr = 1 := by
    have h := Work.SSGRoute.ZDataMup.MupAux.artinSymId_algEquiv (K := K) (L₁ := L) (L₂ := ↥LΩ)
      (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M).symm hcomm hcommΩ' 𝔫K hramL
      Afr (Units.ne_zero A) hcop𝔫
    rw [h, hsym', map_one]
  -- ## the generator of `Gal(LΩ/K)` and the exponents
  haveI hcycΩ : IsCyclic (Gal(↥LΩ/K)) :=
    (MulEquiv.isCyclic (AlgEquiv.autCongr
      (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M).symm)).mp
      (inferInstance : IsCyclic (Gal(L/K)))
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(↥LΩ/K))
  have hexpS : ∀ 𝔮 ∈ s, ∃ t : ℤ, NK.Chebotarev.frobAtPrime (K := K) (L := ↥LΩ) 𝔮 = σ ^ t :=
    fun 𝔮 _ => by
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp (hσ _)
      exact ⟨t, ht.symm⟩
  let sEx : NK.Chebotarev.PrimeIdeal K → ℤ := fun 𝔮 =>
    if h : 𝔮 ∈ s then Classical.choose (hexpS 𝔮 h) else 0
  have hsEx : ∀ 𝔮 ∈ s, NK.Chebotarev.frobAtPrime (K := K) (L := ↥LΩ) 𝔮 = σ ^ (sEx 𝔮) := by
    intro 𝔮 h𝔮
    simp only [sEx, dif_pos h𝔮]
    exact Classical.choose_spec (hexpS 𝔮 h𝔮)
  -- ## the exponent `N` of `𝔟`
  set N : ℤ := ∑ 𝔮 ∈ s, (NK.CFTLib.Arl.exps Afr) 𝔮 * sEx 𝔮 with hNdef
  have hσN : σ ^ N = 1 := by
    have hFfac : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ' A
        = ∏ 𝔮 ∈ s, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ)
            hcommΩ' ((NK.CFTLib.ARL.primeUnit 𝔮) ^ (NK.CFTLib.Arl.exps Afr) 𝔮) := by
      rw [hfac]; exact map_prod _ _ s
    have hprime : ∀ 𝔮 ∈ s, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K)
        (L := ↥LΩ) hcommΩ' (NK.CFTLib.ARL.primeUnit 𝔮)
          = NK.Chebotarev.frobAtPrime (K := K) (L := ↥LΩ) 𝔮 := by
      intro 𝔮 _
      rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, NK.CFTLib.ARL.primeUnit_val]
      exact NK.CFTLib.Arl.artinSym_prime (K := K) (L := ↥LΩ) hcommΩ' 𝔮
    have hmain : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ' A
        = σ ^ N := by
      rw [hFfac, hNdef]
      rw [show (∑ 𝔮 ∈ s, (NK.CFTLib.Arl.exps Afr) 𝔮 * sEx 𝔮)
          = ∑ 𝔮 ∈ s, sEx 𝔮 * (NK.CFTLib.Arl.exps Afr) 𝔮 from
        Finset.sum_congr rfl fun 𝔮 _ => mul_comm _ _]
      have : ∀ 𝔮 ∈ s, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ)
          hcommΩ' ((NK.CFTLib.ARL.primeUnit 𝔮) ^ (NK.CFTLib.Arl.exps Afr) 𝔮)
            = σ ^ (sEx 𝔮 * (NK.CFTLib.Arl.exps Afr) 𝔮) := by
        intro 𝔮 h𝔮
        rw [map_zpow, hprime 𝔮 h𝔮, hsEx 𝔮 h𝔮, zpow_mul]
      rw [Finset.prod_congr rfl this]
      exact NK.NUV2.ARL.SC.finset_prod_zpow s σ (fun 𝔮 => sEx 𝔮 * (NK.CFTLib.Arl.exps Afr) 𝔮)
    rw [← hmain, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply]
    exact hsymΩ
  -- ## `[L:K]` divides `N`
  have hcard : Nat.card (Gal(↥LΩ/K)) = Module.finrank K L := by
    rw [IsGalois.card_aut_eq_finrank K ↥LΩ]
    exact (AlgEquiv.toLinearEquiv (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M)).finrank_eq
  have horder : orderOf σ = Module.finrank K L := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hσ
  have hdvd : (Module.finrank K L : ℤ) ∣ N := by
    rw [← horder]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hσN
  -- ## the auxiliary ideal `𝔅` over `↥E` and `𝔟 = N_{E/K}(𝔅)`
  have hdisj : E ⊓ LΩ = ⊥ := disjoint_iff.mp hEdisj
  have hsurj := IntermediateField.restrictRestrictAlgEquivMapHom_surjective (F := K)
    (E := CyclotomicField M L) LΩ E (by rw [inf_comm]; exact hdisj)
  obtain ⟨τ, hτ⟩ := hsurj σ
  have hτ' : (AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) ↥LΩ)
      (AlgEquiv.restrictScalars K τ) = σ := by
    have hh := hτ
    rw [NK.NUV2.ARL.SC.restrictRestrictAlgEquivMapHom_eq_restrict (K := K) (L := L) M E] at hh
    exact hh
  obtain ⟨𝔅, h𝔅mem, h𝔅sym⟩ := NK.CFTLib.ArtinReciprocityIdeal.surjId_clean ↥E (CyclotomicField M L)
    (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔫K) h𝔫Ene hramE τ
  have hcop𝔅 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId (K := ↥E)
      (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔫K) 𝔅 :=
    (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
      (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔫K) 𝔅).mp h𝔅mem
  set 𝔟 : NK.CFTLib.ArtinReciprocityIdeal.Frac K :=
    NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E)
      (𝔅 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E) with h𝔟def
  have h𝔟sym : NK.CFTLib.Arl.artinSym (K := K) (L := ↥LΩ) hcommΩ'
      (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = σ := by
    have h := Work.SSGRoute.ZDataMup.MupAux.artinSymId_restrict_relNorm (K := K)
      (M := CyclotomicField M L) E LΩ
      (fun a b : Gal(CyclotomicField M L/↥E) => IsMulCommutative.is_comm.comm a b) hcommΩ'
      𝔫K (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔫K)
      (le_refl _)
      (fun 𝔮 h𝔮 => by
        have hM𝔮 : (M : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
          by_contra hM
          exact h𝔮 (NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := ↥E)
            (Ω := CyclotomicField M L) M 𝔮 hM)
        calc Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔫K
            = Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔪 * Ideal.span {(M : 𝓞 ↥E)} := by
              rw [h𝔫Kdef, Ideal.map_mul, map_span_natCast]
          _ ≤ Ideal.span {(M : 𝓞 ↥E)} := Ideal.mul_le_right
          _ ≤ 𝔮.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hM𝔮)
      hramLΩ (𝔅 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E) hcop𝔅
    rw [h𝔅sym, hτ'] at h
    exact h.symm
  have hcop𝔟 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId (K := K) 𝔫K 𝔟 :=
    fracCoprimeId_relNormUnit (K := K) (L := ↥E) hcop𝔅
  -- ## the per-prime elements `X 𝔭`
  let Xa : NK.Chebotarev.PrimeIdeal K → NK.CFTLib.ArtinReciprocityIdeal.Frac K := fun 𝔭 =>
    (NK.CFTLib.ARL.primeUnit 𝔭) ^ (NK.CFTLib.Arl.exps Afr) 𝔭 *
      𝔟 ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭))
  have hXmem : ∀ 𝔭 ∈ s, Xa 𝔭 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
    intro 𝔭 h𝔭
    have hsup𝔭 : ((Ef ⟨𝔭, h𝔭⟩).restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
        ({ζ} : Set (CyclotomicField M L))) = ⊤ := hEfjoin ⟨𝔭, h𝔭⟩
    have hle𝔭 : Ef ⟨𝔭, h𝔭⟩ ≤ E := hEfle ⟨𝔭, h𝔭⟩
    haveI hcyc𝔭 : IsCyclotomicExtension {M} ↥(Ef ⟨𝔭, h𝔭⟩) (CyclotomicField M L) :=
      NK.CFTLib.ARLAlt.isCyclotomicExtension_of_sup_adjoin_zeta (K := K) (L := L) M
        (Ef ⟨𝔭, h𝔭⟩) hsup𝔭
    haveI habel𝔭 : IsAbelianGalois ↥(Ef ⟨𝔭, h𝔭⟩) (CyclotomicField M L) :=
      IsCyclotomicExtension.isAbelianGalois {M} ↥(Ef ⟨𝔭, h𝔭⟩) (CyclotomicField M L)
    haveI hcomm𝔭 : IsMulCommutative (Gal(CyclotomicField M L/↥(Ef ⟨𝔭, h𝔭⟩))) :=
      habel𝔭.toIsMulCommutative
    have hcomm𝔭' : ∀ a b : Gal(CyclotomicField M L/↥(Ef ⟨𝔭, h𝔭⟩)), a * b = b * a :=
      fun a b => IsMulCommutative.is_comm.comm a b
    haveI hgalC𝔭 : IsGalois ↥(Ef ⟨𝔭, h𝔭⟩) ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩)
        (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left) :=
      NK.CFTLib.ARLAlt.isGalois_ofLe_sup (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩)
    haveI hmcCell : IsMulCommutative (Gal(↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩)
        (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left)/↥(Ef ⟨𝔭, h𝔭⟩))) :=
      NK.CFTLib.ARLAlt.isMulCommutative_ofLe_sup (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩) hsup𝔭
    have hcommCell' : ∀ a b : Gal(↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩)
        (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left)/↥(Ef ⟨𝔭, h𝔭⟩)), a * b = b * a :=
      fun a b => IsMulCommutative.is_comm.comm a b
    obtain ⟨𝔓, h𝔓lies, _h𝔓frob, h𝔓norm⟩ :=
      NK.CFTLib.ARLAlt.exists_primeIdeal_isFrobAt_one (Ef ⟨𝔭, h𝔭⟩) 𝔭 (hEfsplit ⟨𝔭, h𝔭⟩)
    -- the modulus at `E𝔭` and the ramification hypotheses for the cell
    have hram𝔭 : ∀ q : NK.Chebotarev.PrimeIdeal ↥(Ef ⟨𝔭, h𝔭⟩),
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥(Ef ⟨𝔭, h𝔭⟩))
          (L := CyclotomicField M L) q →
        DvdPrime (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) q := by
      intro q hq
      have hMq : (M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∈ q.asIdeal := by
        by_contra hM
        exact hq (NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := ↥(Ef ⟨𝔭, h𝔭⟩))
          (Ω := CyclotomicField M L) M q hM)
      calc Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K
          = Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔪 *
              Ideal.span {(M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))} := by
            rw [h𝔫Kdef, Ideal.map_mul, map_span_natCast]
        _ ≤ Ideal.span {(M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))} := Ideal.mul_le_right
        _ ≤ q.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hMq
    have hcellunr : ∀ q : NK.Chebotarev.PrimeIdeal ↥(Ef ⟨𝔭, h𝔭⟩),
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥(Ef ⟨𝔭, h𝔭⟩))
          (L := ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩)
            (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left)) q →
        DvdPrime (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) q := by
      intro q hq
      have hMq : (M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∈ q.asIdeal := by
        by_contra hM
        exact hq (NK.NUV2.ARL.SC.isUnramified_cellAtAux (K := K) (L := L) M
          (Ef ⟨𝔭, h𝔭⟩) hsup𝔭 q hM)
      calc Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K
          = Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔪 *
              Ideal.span {(M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))} := by
            rw [h𝔫Kdef, Ideal.map_mul, map_span_natCast]
        _ ≤ Ideal.span {(M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))} := Ideal.mul_le_right
        _ ≤ q.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hMq
    letI : Algebra ↥(Ef ⟨𝔭, h𝔭⟩) ↥E := NK.NUV2.ARL.SC.algOfLe (Ef ⟨𝔭, h𝔭⟩) E hle𝔭
    letI : IsScalarTower K ↥(Ef ⟨𝔭, h𝔭⟩) ↥E :=
      NK.NUV2.ARL.SC.isScalarTower_algOfLe (Ef ⟨𝔭, h𝔭⟩) E hle𝔭
    letI : FiniteDimensional ↥(Ef ⟨𝔭, h𝔭⟩) ↥E :=
      NK.NUV2.ARL.SC.finiteDimensional_algOfLe (Ef ⟨𝔭, h𝔭⟩) E hle𝔭
    set 𝔠 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥(Ef ⟨𝔭, h𝔭⟩) :=
      NK.CFTLib.ARL.relNormUnit (K := ↥(Ef ⟨𝔭, h𝔭⟩)) (L := ↥E)
        (𝔅 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E) with h𝔠def
    set 𝔘 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥(Ef ⟨𝔭, h𝔭⟩) :=
      (NK.CFTLib.ARL.primeUnit 𝔓) ^ (NK.CFTLib.Arl.exps Afr) 𝔭 *
        𝔠 ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭)) with h𝔘def
    -- `𝔘` is coprime to the modulus
    have h𝔪𝔓 : ¬ DvdPrime (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) 𝔓 := by
      intro h
      have h' : Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K ≤ 𝔓.asIdeal := h
      rw [h𝔫Kdef, Ideal.map_mul, map_span_natCast] at h'
      rcases (Ideal.IsPrime.mul_le 𝔓.isPrime).mp h' with h1 | h1
      · refine hs 𝔭 h𝔭 ?_
        have h2 : 𝔪 ≤ 𝔓.asIdeal.under (𝓞 K) := (Ideal.map_le_iff_le_comap).mp h1
        rwa [← h𝔓lies.over] at h2
      · refine hMnotmem 𝔭 h𝔭 ?_
        have h3 : (M : 𝓞 K) ∈ 𝔓.asIdeal.under (𝓞 K) :=
          (Ideal.mem_under (𝓞 K) 𝔓.asIdeal).mpr
            (by simpa using (Ideal.span_singleton_le_iff_mem 𝔓.asIdeal).mp h1)
        rwa [← h𝔓lies.over] at h3
    have hcop𝔠 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId
        (K := ↥(Ef ⟨𝔭, h𝔭⟩)) (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) 𝔠 :=
      fracCoprimeId_relNormUnit (K := ↥(Ef ⟨𝔭, h𝔭⟩)) (L := ↥E)
        (by
          rw [show Ideal.map (algebraMap (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) (𝓞 ↥E))
                (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K)
              = Ideal.map (algebraMap (𝓞 K) (𝓞 ↥E)) 𝔫K from by
            rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]]
          exact hcop𝔅)
    have hcop𝔘 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId
        (K := ↥(Ef ⟨𝔭, h𝔭⟩)) (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) 𝔘 :=
      (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
        (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) 𝔘).mp (by
        rw [h𝔘def]
        refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ ?_ _) (Subgroup.zpow_mem _ ?_ _)
        · exact Subgroup.subset_closure ⟨𝔓, h𝔪𝔓, rfl⟩
        · exact (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
            (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) 𝔠).mpr hcop𝔠)
    -- `N_{E𝔭/K}𝔘 = X 𝔭`
    have hN𝔘 : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔘 = Xa 𝔭 := by
      have h1 : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩))
          (NK.CFTLib.ARL.primeUnit 𝔓) = NK.CFTLib.ARL.primeUnit 𝔭 := by
        rw [NK.CFTLib.ARL.relNormUnit_primeUnit]
        apply Units.ext
        rw [Units.val_mk0, NK.CFTLib.ARL.primeUnit_val, h𝔓norm]
      have h2 : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔠 = 𝔟 := by
        rw [h𝔠def, h𝔟def]
        exact NK.CFTLib.ARL.relNormUnit_trans (K := K) (E := ↥(Ef ⟨𝔭, h𝔭⟩)) (M := ↥E)
          (𝔅 : (FractionalIdeal (𝓞 ↥E)⁰ ↥E)ˣ)
      show NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔘 =
        (NK.CFTLib.ARL.primeUnit 𝔭) ^ (NK.CFTLib.Arl.exps Afr) 𝔭 *
          𝔟 ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭))
      rw [h𝔘def, map_mul, map_zpow, map_zpow, h1, h2]
    -- `ψ_{LΩ/K}(X 𝔭) = 1`
    have hXsym : NK.CFTLib.Arl.artinSym (K := K) (L := ↥LΩ) hcommΩ'
        (Xa 𝔭 : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
      have h1 : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ'
          (Xa 𝔭) = σ ^ ((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭) *
            σ ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭)) := by
        have hp : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ'
            (NK.CFTLib.ARL.primeUnit 𝔭) = σ ^ (sEx 𝔭) := by
          rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, NK.CFTLib.ARL.primeUnit_val,
            NK.CFTLib.Arl.artinSym_prime (K := K) (L := ↥LΩ) hcommΩ' 𝔭, hsEx 𝔭 h𝔭]
        have hb : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ'
            𝔟 = σ := by
          rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, h𝔟sym]
        show NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ'
          ((NK.CFTLib.ARL.primeUnit 𝔭) ^ (NK.CFTLib.Arl.exps Afr) 𝔭 *
            𝔟 ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭))) =
          σ ^ ((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭) *
            σ ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭))
        rw [map_mul, map_zpow, map_zpow, hp, hb, ← zpow_mul,
          mul_comm (sEx 𝔭) ((NK.CFTLib.Arl.exps Afr) 𝔭)]
      have h2 : σ ^ ((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭) *
          σ ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭)) = 1 := by
        rw [← zpow_add, add_neg_cancel, zpow_zero]
      rw [← NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply (K := K) (L := ↥LΩ) hcommΩ'
        (Xa 𝔭), h1, h2]
    -- the restriction to `LΩ` of the Artin symbol of `𝔘` is trivial
    have hρ : (AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) ↥LΩ)
        (AlgEquiv.restrictScalars K (NK.CFTLib.Arl.artinSym (K := ↥(Ef ⟨𝔭, h𝔭⟩))
          (L := CyclotomicField M L) hcomm𝔭'
          (𝔘 : FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩)))) = 1 := by
      have h := Work.SSGRoute.ZDataMup.MupAux.artinSymId_restrict_relNorm (K := K)
        (M := CyclotomicField M L) (Ef ⟨𝔭, h𝔭⟩) LΩ hcomm𝔭' hcommΩ' 𝔫K
        (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K)
        (le_refl _)
        hram𝔭 hramLΩ (𝔘 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥(Ef ⟨𝔭, h𝔭⟩)) hcop𝔘
      rw [h, hN𝔘, hXsym]
    -- hence the Artin symbol of `𝔘` in the cell `LE𝔭/E𝔭` is trivial
    have hψ : NK.CFTLib.Arl.artinSym (K := ↥(Ef ⟨𝔭, h𝔭⟩))
        (L := ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left))
        hcommCell' (𝔘 : FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩)) = 1 := by
      rw [← Work.SSGRoute.ZDataMup.MupAux.restrictNormalHom_artinSymId_eq_ofLe (K := K) (L := L) M
        (Ef ⟨𝔭, h𝔭⟩) hcomm𝔭' hcommCell'
        (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) hram𝔭
        (𝔘 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥(Ef ⟨𝔭, h𝔭⟩)) hcop𝔘]
      exact NK.NUV2.ARL.SC.restrictNormalHom_eq_one_of_sup (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩) _ hρ
    -- the cell
    have h𝔫𝔭ne : (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot h𝔫Kne
    haveI hnf𝔭 : NumberField ↥(Ef ⟨𝔭, h𝔭⟩) :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField (Ef ⟨𝔭, h𝔭⟩)
    haveI hnfC : NumberField ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left) :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField _
    have hcell_supp : ∀ 𝔮 : HeightOneSpectrum (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)),
        (M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∈ 𝔮.asIdeal →
        DvdPrime (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) 𝔮 := by
      intro 𝔮 h𝔮
      calc Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K
          = Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔪 *
              Ideal.span {(M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))} := by
            rw [h𝔫Kdef, Ideal.map_mul, map_span_natCast]
        _ ≤ Ideal.span {(M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))} := Ideal.mul_le_right
        _ ≤ 𝔮.asIdeal := (Ideal.span_singleton_le_iff_mem 𝔮.asIdeal).mpr h𝔮
    have hcell_lev : ∀ 𝔮 : HeightOneSpectrum (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)),
        (M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∈ 𝔮.asIdeal →
        (WithZero.exp (-(FractionalIdeal.count ↥(Ef ⟨𝔭, h𝔭⟩) 𝔮
          ((Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K :
            FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩))) : ℤ)) :
            WithZero (Multiplicative ℤ))
          ≤ Valued.v (R := 𝔮.adicCompletion ↥(Ef ⟨𝔭, h𝔭⟩))
              (Γ₀ := WithZero (Multiplicative ℤ))
              (((M : ℕ) : 𝔮.adicCompletion ↥(Ef ⟨𝔭, h𝔭⟩))) := by
      intro 𝔮 _
      rw [valued_natCast_eq_exp_neg_count_span M (NeZero.pos M) 𝔮]
      refine WithZero.exp_le_exp.mpr ?_
      have hne : ((Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K :
          Ideal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) :
            FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩)) ≠ 0 :=
        FractionalIdeal.coeIdeal_ne_zero.mpr h𝔫𝔭ne
      have hle : ((Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K :
            Ideal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) :
              FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩)) ≤
          ((Ideal.span {(M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))} : Ideal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) :
            FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩)) :=
        (FractionalIdeal.coeIdeal_le_coeIdeal (K := ↥(Ef ⟨𝔭, h𝔭⟩))).mpr (by
          calc Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K
              = Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔪 *
                  Ideal.span {(M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))} := by
                rw [h𝔫Kdef, Ideal.map_mul, map_span_natCast]
            _ ≤ Ideal.span {(M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))} := Ideal.mul_le_right)
      exact neg_le_neg (FractionalIdeal.count_mono (K := ↥(Ef ⟨𝔭, h𝔭⟩)) (v := 𝔮) hne hle)
    have hcell_ram : ∀ q : NK.Chebotarev.PrimeIdeal ↥(Ef ⟨𝔭, h𝔭⟩),
        Ideal.ramificationIdxIn q.asIdeal
            (𝓞 ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left)) ≠ 1 →
        DvdPrime (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) q := by
      intro q hq
      exact hcellunr q (fun hunr => hq
        ((isUnramified_iff_ramificationIdxIn_eq_one_Id (K := ↥(Ef ⟨𝔭, h𝔭⟩))
          (L := ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left))
          q).mp hunr))
    have hcell : 𝔘 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRayId
          (K := ↥(Ef ⟨𝔭, h𝔭⟩)) (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := ↥(Ef ⟨𝔭, h𝔭⟩))
          (L := ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left))
          (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) :=
      cyclotomicCellKernelLeId_clean ↥(Ef ⟨𝔭, h𝔭⟩) (CyclotomicField M L) M
        (NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left)
        (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) h𝔫𝔭ne
        hcell_supp hcell_lev hcell_ram 𝔘 hcop𝔘 hψ
    -- descent to `K`
    have hPR := Work.SSGRoute.ZDataMup.MupAux.principalRayId_map_relNormUnit_le (K := K)
      (E := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔪
      (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) h𝔪 h𝔫𝔭ne
      (by rw [Ideal.map_mul, map_span_natCast]; exact Ideal.mul_le_left)
    have hNR := normRayId_cell_descent (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩)
      (Ideal.map (algebraMap (𝓞 K) (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))) 𝔫K) 𝔪 h𝔪
      (by rw [Ideal.map_mul, map_span_natCast]; exact Ideal.mul_le_left)
    have hmem : Xa 𝔭 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
      have hmap := Subgroup.mem_map_of_mem
        (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩))) hcell
      rw [Subgroup.map_sup] at hmap
      rw [hN𝔘] at hmap
      exact (sup_le (le_trans hPR le_sup_left) (le_trans hNR le_sup_right)) hmap
    exact hmem
  -- ## bookkeeping
  have hXprod : ∏ 𝔭 ∈ s, Xa 𝔭 = A * 𝔟 ^ (-N) := by
    have h1 : (∏ 𝔭 ∈ s, Xa 𝔭) = (∏ 𝔭 ∈ s,
        (NK.CFTLib.ARL.primeUnit 𝔭) ^ (NK.CFTLib.Arl.exps Afr) 𝔭) *
        ∏ 𝔭 ∈ s, 𝔟 ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭)) :=
      Finset.prod_mul_distrib
    rw [h1, ← hfac, NK.NUV2.ARL.SC.finset_prod_zpow]
    congr 1
    rw [hNdef, ← Finset.sum_neg_distrib]
  have hprodmem : ∏ 𝔭 ∈ s, Xa 𝔭 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 :=
    Subgroup.prod_mem _ (fun 𝔭 h𝔭 => hXmem 𝔭 h𝔭)
  have hcop𝔟𝔪 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId (K := K) 𝔪 𝔟 :=
    fracCoprimeId_mono (by rw [h𝔫Kdef]; exact Ideal.mul_le_left) hcop𝔟
  have hfin : Module.finrank K ↥LΩ = Module.finrank K L := by
    rw [← IsGalois.card_aut_eq_finrank K ↥LΩ, hcard]
  have hbase : 𝔟 ^ Module.finrank K L ∈ NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K)
      (L := L) 𝔪 := by
    have h := pow_finrank_mem_normRayId (K := K) (L := ↥LΩ) 𝔪 hcop𝔟𝔪
    rw [hfin, Work.SSGRoute.ZDataMup.MupAux.normRayId_LImage_eq (K := K) (L := L) M 𝔪] at h
    exact h
  obtain ⟨k, hk⟩ := hdvd
  have h𝔟N : 𝔟 ^ N ∈ NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
    rw [hk, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ hbase k
  have hAeq : A = (∏ 𝔭 ∈ s, Xa 𝔭) * 𝔟 ^ N := by
    rw [hXprod]; group
  rw [hAeq]
  exact Subgroup.mul_mem _ hprodmem (Subgroup.mem_sup_right h𝔟N)

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
