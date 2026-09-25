import Mathlib
import Submission.NK.NUV2.ARL.Defs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.AbelianReduction
import Submission.NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient

namespace NK.NUV2.ARL

open NK.Chebotarev
open NumberField
open scoped NumberField

section Tower

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Unramifiedness descends to intermediate fields.**  If a prime of `K` is unramified in `L`,
it is unramified in every intermediate field `K ⊆ M ⊆ L`. -/
theorem ramificationIdxIn_eq_one_of_intermediateField
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [IsGalois K ↥M]
    (p : PrimeIdeal K)
    (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1) :
    Ideal.ramificationIdxIn p.asIdeal (𝓞 ↥M) = 1 := by
  obtain ⟨P, hP⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := ↥M) p
  obtain ⟨Q, hQ⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := ↥M) (L := L) P
  letI hMSA₁ : MulSemiringAction (Gal(↥M/K)) (𝓞 ↥M) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K ↥M (𝓞 ↥M)
  letI hMSA₂ : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  letI hMSA₃ : MulSemiringAction (Gal(L/↥M)) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 ↥M) ↥M L (𝓞 L)
  haveI hGG₁ : IsGaloisGroup (Gal(↥M/K)) (𝓞 K) (𝓞 ↥M) :=
    IsGaloisGroup.of_isFractionRing (Gal(↥M/K)) (𝓞 K) (𝓞 ↥M) K ↥M
  haveI hGG₂ : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
  haveI hGG₃ : IsGaloisGroup (Gal(L/↥M)) (𝓞 ↥M) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/↥M)) (𝓞 ↥M) (𝓞 L) ↥M L
  haveI hN : Nonempty ↑(P.asIdeal.primesOver (𝓞 L)) := ⟨⟨Q.asIdeal, Q.2, hQ⟩⟩
  have hmul := Ideal.ramificationIdxIn_mul_ramificationIdxIn (A := 𝓞 K) (B := 𝓞 ↥M)
    (C := 𝓞 L) (p := p.asIdeal) (P := P.asIdeal) (hp := hP) (G := Gal(↥M/K))
    (GAC := Gal(L/K)) (GBC := Gal(L/↥M))
  rw [h] at hmul
  exact Nat.eq_one_of_dvd_one ⟨_, hmul.symm⟩

/-- **The product condition of a conductor descends to intermediate normal subextensions.**  If
every prime coprime to `m` is unramified in `L` and the Artin symbol kills the principal ideals
congruent to `1` modulo `m` in `L/K`, then the same holds in every intermediate extension `M/K`
which is normal over `K` (the Frobenius elements of `M/K` are the restrictions of Frobenius
elements of `L/K`). -/
theorem artinKillsPrincipal_of_intermediateField
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [Normal K ↥M]
    {m : ℕ}
    (hram : ∀ p : PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1)
    (h : NK.CFTLib.artinKillsPrincipal K L m) :
    NK.CFTLib.artinKillsPrincipal K ↥M m := by
  classical
  haveI : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  letI hMSA : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGG : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
  intro a ha hpos s e τ hs hfac hτ
  have hlift : ∀ p : PrimeIdeal K, ∃ σ : Gal(L/K),
      (p ∈ s → IsFrobAtPrime (K := K) (L := L) p σ) ∧
      (p ∈ s → (AlgEquiv.restrictNormalHom ↥M) σ = τ p) := by
    intro p
    by_cases hp : p ∈ s
    · obtain ⟨Q, hQover, hQτ⟩ := hτ p hp
      obtain ⟨P, hPover⟩ :=
        Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := ↥M) (L := L) Q
      have hPoverK : P.asIdeal.LiesOver p.asIdeal := by
        haveI := hPover
        haveI := hQover
        exact Ideal.LiesOver.trans (𝔓 := P.asIdeal) (P := Q.asIdeal) (p := p.asIdeal)
      obtain ⟨σ, hσ⟩ := NK.Chebotarev.exists_isFrobAt (K := K) (L := L) p P hPoverK
      have hQram : Q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
        have h1 : Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = P.asIdeal.ramificationIdx (𝓞 K) :=
          Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) p.asIdeal P.asIdeal
            (Gal(L/K))
        have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 ↥M) (T := 𝓞 L)
          (q := Q.asIdeal) (r := P.asIdeal)
        rw [← h1, hram p (hs p hp)] at htower
        exact Nat.eq_one_of_dvd_one ⟨_, htower⟩
      have h1 : IsFrobAt (K := K) (L := ↥M) Q ((AlgEquiv.restrictNormalHom ↥M) σ) := by
        have h2 := NK.Chebotarev.IsFrobAtRestrictNormalHom (K := K) (M := L) M hPoverK hσ
        rwa [show P.under (𝓞 ↥M) = Q from
          IsDedekindDomain.HeightOneSpectrum.ext (by
            rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, hPover.over])] at h2
      refine ⟨σ, fun _ => ⟨P, hPoverK, hσ⟩, fun _ => ?_⟩
      exact IsFrobAt.eq_of_isFrobAt (K := K) (L := ↥M) (p := p) (P := Q) hQover hQram h1 hQτ
    · exact ⟨1, fun h => absurd h hp, fun h => absurd h hp⟩
  choose σ hσ hσres using hlift
  have hprod := h a ha hpos s e σ hs hfac (fun p hp => hσ p hp)
  have hres : (AlgEquiv.restrictNormalHom ↥M) ((s.toList.map (fun p => σ p ^ e p)).prod)
      = (s.toList.map (fun p => τ p ^ e p)).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    show (AlgEquiv.restrictNormalHom ↥M) (σ p ^ e p) = τ p ^ e p
    rw [map_pow, hσres p (Finset.mem_toList.mp hp)]
  rw [hprod, map_one] at hres
  exact hres.symm


end Tower

theorem abelianWeakToStrong
    (hcyc : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))] (m : ℕ), 0 < m →
      (∀ p : NK.Chebotarev.PrimeIdeal K, (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
        Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1) →
      NK.CFTLib.artinKillsPrincipal K L m →
      ∃ m' : ℕ, 0 < m' ∧
        (∀ p : NK.Chebotarev.PrimeIdeal K, (m' : NumberField.RingOfIntegers K) ∈ p.asIdeal →
          Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) ≠ 1) ∧
        NK.CFTLib.artinKillsPrincipal K L m') :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L], (∀ a b : Gal(L/K), a * b = b * a) → (m : ℕ) → 0 < m →
      (∀ p : NK.Chebotarev.PrimeIdeal K, (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
        Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1) →
      NK.CFTLib.artinKillsPrincipal K L m →
      ∃ m' : ℕ, 0 < m' ∧
        (∀ p : NK.Chebotarev.PrimeIdeal K, (m' : NumberField.RingOfIntegers K) ∈ p.asIdeal →
          Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) ≠ 1) ∧
        NK.CFTLib.artinKillsPrincipal K L m' := by
  intro K L _ _ _ _ _ _ _ hcomm m hm hram hkills
  classical
  haveI hcommI : IsMulCommutative (Gal(L/K)) := IsMulCommutative.of_comm hcomm
  letI : Fintype (Subgroup Gal(L/K)) := Fintype.ofFinite _
  -- the group-theoretic input: an element of `Gal(L/K)` is trivial as soon as its images in all
  -- the cyclic quotients are trivial
  have hgrp : ∀ g : Gal(L/K), g ≠ 1 →
      ∃ H : Subgroup Gal(L/K), IsCyclic (Gal(L/K) ⧸ H) ∧ g ∉ H := by
    have hbot : (⨅ H : {H : Subgroup Gal(L/K) // IsCyclic (Gal(L/K) ⧸ H)},
        (H.1 : Subgroup Gal(L/K))) = ⊥ := by
      letI : CommGroup (Gal(L/K)) :=
        { (inferInstance : Group (Gal(L/K))) with mul_comm := fun a b => hcomm a b }
      exact NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient
    intro g hg
    have hmem : g ∉ (⨅ H : {H : Subgroup Gal(L/K) // IsCyclic (Gal(L/K) ⧸ H)},
        (H.1 : Subgroup Gal(L/K))) := by
      rw [hbot]
      exact hg
    rw [Subgroup.mem_iInf] at hmem
    simp only [not_forall] at hmem
    obtain ⟨H, hH⟩ := hmem
    exact ⟨H.1, H.2, hH⟩
  -- for every subgroup `H` of `Gal(L/K)` with cyclic quotient, a modulus for the cyclic
  -- subextension `L^H/K` which is supported on the primes ramified in `L^H/K` and still
  -- satisfies the product condition
  have hH' : ∀ H : Subgroup Gal(L/K), ∃ m' : ℕ, 0 < m' ∧
      (IsCyclic (Gal(L/K) ⧸ H) →
        (∀ p : PrimeIdeal K, (m' : 𝓞 K) ∈ p.asIdeal →
          Ideal.ramificationIdxIn p.asIdeal (𝓞 ↥(IntermediateField.fixedField H)) ≠ 1) ∧
        NK.CFTLib.artinKillsPrincipal K ↥(IntermediateField.fixedField H) m') ∧
      (¬ IsCyclic (Gal(L/K) ⧸ H) → m' = 1) := by
    intro H
    by_cases hHcyc : IsCyclic (Gal(L/K) ⧸ H)
    · haveI : FiniteDimensional K ↥(IntermediateField.fixedField H) := inferInstance
      haveI : NumberField ↥(IntermediateField.fixedField H) := inferInstance
      haveI : IsCyclic (Gal(↥(IntermediateField.fixedField H)/K)) :=
        (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient H).symm).mpr hHcyc
      have hdiff_ne : Ideal.absNorm
          (differentIdeal (𝓞 K) (𝓞 ↥(IntermediateField.fixedField H))) ≠ 0 := by
        rw [Ideal.absNorm_ne_zero_iff]
        exact Ring.HasFiniteQuotients.finiteQuotient
          (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 ↥(IntermediateField.fixedField H)))
      have hramM : ∀ p : PrimeIdeal K,
          ((m * Ideal.absNorm (differentIdeal (𝓞 K)
            (𝓞 ↥(IntermediateField.fixedField H))) : ℕ) : 𝓞 K) ∉ p.asIdeal →
          Ideal.ramificationIdxIn p.asIdeal
            (𝓞 ↥(IntermediateField.fixedField H)) = 1 := by
        intro p hp
        refine NK.CFTLib.ramificationIdxIn_eq_one_of_absNorm_differentIdeal_notMem
          (L := ↥(IntermediateField.fixedField H)) p ?_
        intro hmem
        apply hp
        push_cast
        exact p.asIdeal.mul_mem_left _ hmem
      have hkillsM : NK.CFTLib.artinKillsPrincipal K ↥(IntermediateField.fixedField H)
          (m * Ideal.absNorm (differentIdeal (𝓞 K)
            (𝓞 ↥(IntermediateField.fixedField H)))) :=
        (artinKillsPrincipal_of_intermediateField (K := K) (L := L)
          (M := IntermediateField.fixedField H) (m := m) hram hkills).mono
            (dvd_mul_right m _)
      obtain ⟨m', hm'pos, hsupp', hkill'⟩ := hcyc K ↥(IntermediateField.fixedField H)
        (m * Ideal.absNorm (differentIdeal (𝓞 K)
          (𝓞 ↥(IntermediateField.fixedField H))))
        (Nat.mul_pos hm (Nat.pos_of_ne_zero hdiff_ne)) hramM hkillsM
      exact ⟨m', hm'pos, fun _ => ⟨hsupp', hkill'⟩, fun hc => absurd hHcyc hc⟩
    · exact ⟨1, Nat.one_pos, fun hc => absurd hc hHcyc, fun _ => rfl⟩
  choose mH hmHpos hmH using hH'
  set m' : ℕ := ∏ H : Subgroup Gal(L/K), mH H with hm'def
  refine ⟨m', ?_, ?_, ?_⟩
  · rw [hm'def]
    exact Finset.prod_pos fun H _ => hmHpos H
  · -- the support of `m'` is contained in the primes ramified in `L/K`
    intro p hp
    rw [hm'def] at hp
    push_cast at hp
    obtain ⟨H, -, hHmem⟩ := (Ideal.IsPrime.prod_mem_iff (s := Finset.univ)
      (x := fun H : Subgroup Gal(L/K) => ((mH H : ℕ) : 𝓞 K))).mp (by simpa using hp)
    have hcycH : IsCyclic (Gal(L/K) ⧸ H) := by
      by_contra hc
      have h1 : (1 : 𝓞 K) ∈ p.asIdeal := by
        simpa [(hmH H).2 hc] using hHmem
      exact p.isPrime.ne_top (Ideal.eq_top_iff_one p.asIdeal |>.mpr h1)
    have hMne : Ideal.ramificationIdxIn p.asIdeal
        (𝓞 ↥(IntermediateField.fixedField H)) ≠ 1 := ((hmH H).1 hcycH).1 p hHmem
    intro hL
    exact hMne (ramificationIdxIn_eq_one_of_intermediateField
      (M := IntermediateField.fixedField H) p hL)
  · -- the product condition for `m'` holds because its restrictions to the cyclic quotients do
    intro a ha hpos s e σ hs hfac hσ
    by_contra hne
    obtain ⟨H, hHcyc, hHnot⟩ := hgrp _ hne
    haveI : FiniteDimensional K ↥(IntermediateField.fixedField H) := inferInstance
    haveI : NumberField ↥(IntermediateField.fixedField H) := inferInstance
    have hdvd : mH H ∣ m' := by
      rw [hm'def]
      exact Finset.dvd_prod_of_mem (fun H => mH H) (Finset.mem_univ H)
    have hdvd' : ((mH H : ℕ) : 𝓞 K) ∣ ((m' : ℕ) : 𝓞 K) := by
      obtain ⟨c, hc⟩ := hdvd
      exact ⟨(c : 𝓞 K), by rw [hc]; push_cast; ring⟩
    have hspan : Ideal.span {((m' : ℕ) : 𝓞 K)} ≤ Ideal.span {((mH H : ℕ) : 𝓞 K)} :=
      Ideal.span_singleton_le_span_singleton.mpr hdvd'
    have hs' : ∀ p ∈ s, ((mH H : ℕ) : 𝓞 K) ∉ p.asIdeal := by
      intro p hp hmem
      apply hs p hp
      obtain ⟨c, hc⟩ := hdvd'
      rw [hc]
      exact p.asIdeal.mul_mem_right _ hmem
    have hkillM : NK.CFTLib.artinKillsPrincipal K
        ↥(IntermediateField.fixedField H) (mH H) := ((hmH H).1 hHcyc).2
    have hprod := hkillM a (hspan ha) hpos s e
      (fun p => (AlgEquiv.restrictNormalHom ↥(IntermediateField.fixedField H)) (σ p))
      hs' hfac (fun p hp => NK.CFTLib.exists_isFrobAtPrime_restrict
        (IntermediateField.fixedField H) (hσ p hp))
    have hres : (AlgEquiv.restrictNormalHom ↥(IntermediateField.fixedField H))
        ((s.toList.map (fun p => σ p ^ e p)).prod)
        = (s.toList.map (fun p =>
            ((AlgEquiv.restrictNormalHom ↥(IntermediateField.fixedField H)) (σ p))
              ^ e p)).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left fun p _ => map_pow _ _ _
    have hker : (s.toList.map (fun p => σ p ^ e p)).prod ∈
        (AlgEquiv.restrictNormalHom ↥(IntermediateField.fixedField H)).ker := by
      rw [MonoidHom.mem_ker, hres]
      exact hprod
    rw [IntermediateField.restrictNormalHom_ker,
      IntermediateField.fixingSubgroup_fixedField H] at hker
    exact hHnot hker

end NK.NUV2.ARL
