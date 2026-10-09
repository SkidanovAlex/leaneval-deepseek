import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.absDiscrQBar
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.PlaceBelow
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.prime_dvd_discr_of_isRamifiedIn_algebraicClosure
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.localizationExp
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.differentIdeal_count_le_clean_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A `sorry`-free Hermite–Minkowski chain, avoiding the tainted `differentIdeal_count_le_proved`

The workspace files `absDiscrQBar.lean` / `exists_absDiscr_le_proved.lean` / `finiteHM.lean`
discharge the Hermite–Minkowski input of `Finite ↥(X¹_S)` from the *statement stub*
`differentIdeal_count_le_proved`, which is still a `sorry`.  This file reproduces the same chain
using instead the `sorry`-free input `differentIdeal_count_le_finrank` (the crude per-prime bound
`count_P(𝔡) ≤ n(1+n²)`), giving an `sorry`-free `finite_of_bddDegree_unamifiedOutside_clean`.

(Note: the *alternative* route through the localisation-based invariant
`FinitenessHM.locExp` is **wrong** — the trace dual defining `differentIdeal ℤ_(p) (𝓞 K)_P` uses
the *global* trace `Tr_{K/ℚ}`, which is not the local trace `Tr_{K_P/ℚ_p}`, so that exponent is
not the `P`-exponent of the global different.  The correct notion is the one of the completion,
and `differentIdeal_count_le_finrank` is proved by whichever of the two routes is used.)
-/

open NumberField UniqueFactorizationMonoid
open scoped NumberField

set_option linter.style.haveILetI false

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

private lemma expBound_mono' {a b : ℕ} (hab : a ≤ b) : expBound a ≤ expBound b := by
  unfold expBound
  gcongr

private lemma isFinPlace_comap_iff' {A Ω' : Type} [Field A] [Field Ω'] [Algebra ℚ A]
    [Algebra ℚ Ω'] (f : A →+* Ω') (hf : f.comp (algebraMap ℚ A) = algebraMap ℚ Ω')
    (B : ValuationSubring Ω') :
    SSGRoute.IsFinPlace ℚ (B.comap f) ↔ SSGRoute.IsFinPlace ℚ B := by
  simp only [SSGRoute.IsFinPlace, ValuationSubring.comap_comap, hf]

private lemma isFinPlace_pullback' {A : Type} [Field A] [Algebra ℚ A]
    (σ : A ≃ₐ[ℚ] SSGRoute.QBar) (B : ValuationSubring SSGRoute.QBar) :
    SSGRoute.IsFinPlace ℚ (B.comap (σ : A →+* SSGRoute.QBar)) ↔ SSGRoute.IsFinPlace ℚ B := by
  have hcomp : ((σ : A →+* SSGRoute.QBar)).comp (algebraMap ℚ A) = algebraMap ℚ SSGRoute.QBar := by
    ext r
    exact σ.commutes r
  exact isFinPlace_comap_iff' (σ : A →+* SSGRoute.QBar) hcomp B

/-- **The classical bound on the exponent of a rational prime in the different ideal**,
re-exported under the name used by the rest of this chain. -/
theorem differentIdeal_count_le_clean {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime)
    (hlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    (UniqueFactorizationMonoid.normalizedFactors
        (differentIdeal ℤ (NumberField.RingOfIntegers K))).count P ≤
      P.ramificationIdx ℤ * (1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ)) :=
  differentIdeal_count_le_clean_bound p P hP hlies

/-- **The discriminant exponent bound**, from the crude per-prime different bound
`count_P(𝔡) ≤ n(1+n²)` (`n = finrank ℚ K`): the copy of `absDiscrQBar.padicValNat_discr_le`
suited to the crude hypothesis. -/
theorem padicValNat_discr_le_crude {K : Type*} [Field K] [NumberField K] (q : ℕ) [Fact q.Prime]
    (hdiff : ∀ (P : Ideal (𝓞 K)), P.IsPrime → P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) →
      (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ≤
        Module.finrank ℚ K * (1 + Module.finrank ℚ K * Module.finrank ℚ K)) :
    padicValNat q (NumberField.discr K).natAbs ≤ expBound (Module.finrank ℚ K) := by
  classical
  set n := Module.finrank ℚ K with hn
  set pp : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ) with hpp
  haveI hppMax : pp.IsMaximal := by
    rw [hpp]
    exact Prime.isMaximal_span_singleton (Nat.prime_iff_prime_int.mp Fact.out)
  have hpp0 : pp ≠ ⊥ := by
    rw [hpp, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  set s : Finset (Ideal (𝓞 K)) :=
    (UniqueFactorizationMonoid.normalizedFactors
      (differentIdeal ℤ (𝓞 K))).toFinset.filter (fun P => P.LiesOver pp) with hs
  have hne : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
  rw [Commons.NumberTheory.NumberField.discr_padicValNat_eq_sum_over_p_count_mul_inertiaDeg q]
  change (∑ P ∈ s, (UniqueFactorizationMonoid.normalizedFactors
      (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ) ≤ expBound n
  have hcard : s.card ≤ n := by
    have hsub : s ⊆ IsDedekindDomain.primesOverFinset pp (𝓞 K) := by
      intro P hP
      rw [hs, Finset.mem_filter, Multiset.mem_toFinset] at hP
      obtain ⟨hmem, hlie⟩ := hP
      have hprime : P.IsPrime := (Ideal.mem_normalizedFactors_iff hne).mp hmem |>.1
      rw [IsDedekindDomain.mem_primesOverFinset_iff hpp0]
      exact ⟨hprime, hlie⟩
    calc s.card ≤ (IsDedekindDomain.primesOverFinset pp (𝓞 K)).card := Finset.card_le_card hsub
      _ ≤ Module.finrank ℚ K := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hpp0
      _ = n := hn.symm
  have hterm : ∀ P ∈ s,
      (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 K))).count P *
        P.inertiaDeg ℤ ≤ (n * (1 + n * n)) * n := by
    intro P hP
    rw [hs, Finset.mem_filter, Multiset.mem_toFinset] at hP
    obtain ⟨hmem, hlie⟩ := hP
    have hprime : P.IsPrime := (Ideal.mem_normalizedFactors_iff hne).mp hmem |>.1
    have hleP : differentIdeal ℤ (𝓞 K) ≤ P := (Ideal.mem_normalizedFactors_iff hne).mp hmem |>.2
    have hPne : P ≠ ⊥ := by
      intro hbot
      exact hne (le_bot_iff.mp (by simpa [hbot] using hleP))
    haveI : P.IsPrime := hprime
    haveI : P.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot P hPne
    haveI : P.LiesOver pp := hlie
    have hf : P.inertiaDeg ℤ ≤ n := by
      have h1 : Ideal.inertiaDeg' pp P ≤ Module.finrank ℚ K :=
        Ideal.inertiaDeg_le_finrank (𝓞 K) ℚ K P hpp0
      have h2 : Ideal.inertiaDeg' pp P = P.inertiaDeg ℤ :=
        Ideal.inertiaDeg'_eq_inertiaDeg (p := pp) (P := P)
      rw [h2] at h1
      rwa [hn]
    calc (UniqueFactorizationMonoid.normalizedFactors
            (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ
        ≤ (n * (1 + n * n)) * P.inertiaDeg ℤ :=
          Nat.mul_le_mul_right _ (hdiff P hprime hlie)
      _ ≤ (n * (1 + n * n)) * n := Nat.mul_le_mul_left _ hf
  calc ∑ P ∈ s, (UniqueFactorizationMonoid.normalizedFactors
        (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ
      ≤ s.card • ((n * (1 + n * n)) * n) := Finset.sum_le_card_nsmul s _ _ hterm
    _ = s.card * ((n * (1 + n * n)) * n) := by rw [nsmul_eq_mul, Nat.cast_id]
    _ ≤ n * ((n * (1 + n * n)) * n) := Nat.mul_le_mul_right _ hcard
    _ = expBound n := rfl

/-- **The discriminant bound over `ℚ̄`, in prime-set form** (`absDiscrQBar.abs_discr_le_QBar_primeSet`
with the different bound re-pointed at the axiom-clean `differentIdeal_count_le_finrank`). -/
theorem abs_discr_le_QBar_primeSet_clean (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (n : ℕ) :
    ∀ (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K],
      Module.finrank ℚ K ≤ n →
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
        SSGRoute.IsRamifiedIn ℚ K B → ∃ q ∈ P, B.valuation (q : SSGRoute.QBar) < 1) →
      (NumberField.discr K).natAbs ≤ ∏ p ∈ P, p ^ expBound n := by
  classical
  intro K hK hdeg hram
  haveI : NumberField K := NumberField.of_module_finite ℚ K
  set N : ℕ := (NumberField.discr K).natAbs with hN
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)
  have hsupp : ∀ q : ℕ, q.Prime → q ∉ P → padicValNat q N = 0 := by
    intro q hq hqmem
    haveI : Fact q.Prime := ⟨hq⟩
    rw [hN]
    by_contra hne
    have hdvd : q ∣ (NumberField.discr K).natAbs := by
      have h1 : q ^ padicValNat q ((NumberField.discr K).natAbs) ∣
          (NumberField.discr K).natAbs := pow_padicValNat_dvd
      have h2 : q ∣ q ^ padicValNat q ((NumberField.discr K).natAbs) :=
        dvd_pow_self q (Nat.pos_iff_ne_zero.mp (Nat.pos_of_ne_zero hne))
      exact dvd_trans h2 h1
    obtain ⟨B, hBfin, hBval, hBram⟩ :=
      isRamifiedIn_of_dvd_discr_natAbs_proved K q hq hdvd
    obtain ⟨q', hq'P, hq'val⟩ := hram B hBfin hBram
    have h1 : Work.SSGRoute.placePrime B hBfin = ⟨q, hq⟩ :=
      Work.SSGRoute.placePrime_eq_of_val_lt_one q B hBfin hBval
    haveI : Fact q'.Prime := ⟨hP q' hq'P⟩
    have h2 : Work.SSGRoute.placePrime B hBfin = ⟨q', (hP q' hq'P)⟩ :=
      Work.SSGRoute.placePrime_eq_of_val_lt_one q' B hBfin hq'val
    have hqq' : q = q' := congrArg Subtype.val (h1.symm.trans h2)
    exact hqmem (hqq' ▸ hq'P)
  have h1 : N.factorization.support ⊆ P := by
    intro q hq
    rw [Finsupp.mem_support_iff] at hq
    have hqprime : q.Prime := by
      by_contra hq'
      exact hq (Nat.factorization_eq_zero_of_not_prime N hq')
    by_contra hqmem
    exact hq (by rw [Nat.factorization_def N hqprime]; exact hsupp q hqprime hqmem)
  have hmain : N = ∏ p ∈ P, p ^ padicValNat p N := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
    rw [Finsupp.prod]
    refine (Finset.prod_subset h1 ?_).trans ?_
    · intro q _ hqnot
      rw [Finsupp.notMem_support_iff.mp hqnot, pow_zero]
    · exact Finset.prod_congr rfl (fun q hq => by
        rw [Nat.factorization_def N (hP q hq)])
  calc N = ∏ p ∈ P, p ^ padicValNat p N := hmain
    _ ≤ ∏ p ∈ P, p ^ expBound n := by
        refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) (fun p hp => ?_)
        haveI : Fact p.Prime := ⟨hP p hp⟩
        refine Nat.pow_le_pow_right (Nat.Prime.pos (hP p hp)) ?_
        refine le_trans (padicValNat_discr_le p
          (fun P' hP' hlie => differentIdeal_count_le_clean p P' hP' hlie)) ?_
        exact expBound_mono' hdeg

/-- **The discriminant bound over an algebraic closure of `ℚ`, prime-set form** — the
`absDiscrQBar.abs_discr_le_primeSet` statement with the axiom-clean different bound. -/
theorem abs_discr_le_primeSet_clean (A : Type) [Field A] [CharZero A] [IsAlgClosure ℚ A]
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (n : ℕ) :
    ∃ C : ℕ, ∀ (K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F}),
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.2
      Module.finrank ℚ K ≤ n →
      (∀ B : ValuationSubring A, SSGRoute.IsFinPlace ℚ B → SSGRoute.IsRamifiedIn ℚ K B →
        ∃ q ∈ P, B.valuation (q : A) < 1) →
      |NumberField.discr K| ≤ C := by
  classical
  obtain ⟨σ⟩ : Nonempty (A ≃ₐ[ℚ] SSGRoute.QBar) := ⟨IsAlgClosure.equiv ℚ A SSGRoute.QBar⟩
  refine ⟨∏ p ∈ P, p ^ expBound n, ?_⟩
  intro K hdeg hram
  set K' : IntermediateField ℚ SSGRoute.QBar := K.1.map σ.toAlgHom with hK'def
  haveI hKfin : FiniteDimensional ℚ K.1 := K.2
  haveI hK'fin : FiniteDimensional ℚ K' :=
    FiniteDimensional.of_surjective (IntermediateField.equivMap K.1 σ.toAlgHom).toLinearMap
      (IntermediateField.equivMap K.1 σ.toAlgHom).surjective
  have hdeg' : Module.finrank ℚ K' ≤ n := by
    rw [← LinearEquiv.finrank_eq (IntermediateField.equivMap K.1 σ.toAlgHom).toLinearEquiv]
    exact hdeg
  have hram' : ∀ B' : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B' →
      SSGRoute.IsRamifiedIn ℚ K' B' → ∃ q ∈ P, B'.valuation (q : SSGRoute.QBar) < 1 := by
    intro B' hB'fin hB'ram
    have hBfin : SSGRoute.IsFinPlace ℚ (B'.comap (σ : A →+* SSGRoute.QBar)) :=
      (isFinPlace_pullback' σ B').mpr hB'fin
    have hBram : SSGRoute.IsRamifiedIn ℚ K.1 (B'.comap (σ : A →+* SSGRoute.QBar)) :=
      (isRamifiedIn_comap_algEquiv_proved A σ K.1 B').mpr hB'ram
    obtain ⟨q, hqP, hqval⟩ := hram (B'.comap (σ : A →+* SSGRoute.QBar)) hBfin hBram
    refine ⟨q, hqP, ?_⟩
    have hσq : (σ : A →+* SSGRoute.QBar) (q : A) = (q : SSGRoute.QBar) := map_natCast _ _
    rw [← hσq, ← comap_valuation_lt_one_iff' (σ : A →+* SSGRoute.QBar) B' (q : A)]
    exact hqval
  have hcore := abs_discr_le_QBar_primeSet_clean P hP n K' hdeg' hram'
  have hdisc : NumberField.discr K.1 = NumberField.discr K' :=
    NumberField.discr_eq_discr_of_algEquiv ↥K.1 (IntermediateField.equivMap K.1 σ.toAlgHom)
  rw [hdisc]
  refine le_trans (le_of_eq (Int.natCast_natAbs (NumberField.discr K')).symm) ?_
  exact_mod_cast hcore

/-- **A uniform bound for the absolute discriminant of `L/k` of bounded degree with ramification
confined to `S`** — `exists_absDiscr_le_proved` with the axiom-clean discriminant bound. -/
theorem exists_absDiscr_le_clean
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [CharZero Ω]
    (S : Finset (ValuationSubring Ω)) (hS : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (n : ℕ) :
    ∃ C : ℕ, ∀ (L : IntermediateField k Ω) [FiniteDimensional k L],
      Module.finrank k L ≤ n →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → SSGRoute.IsRamifiedIn k L B →
        ∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (∀ (h : FiniteDimensional ℚ ↥(L.restrictScalars ℚ)),
        |@NumberField.discr ↥(L.restrictScalars ℚ) _ (@NumberField.mk _ _ _ h)| ≤ (C : ℤ)) := by
  classical
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ k Ω
  haveI : FiniteDimensional ℚ ↥(kview k Ω) := kview_finiteDimensional k Ω
  let P : Finset ℕ := S.attach.image (fun A => pof k Ω A.1 (hS A.1 A.2)) ∪
    (NumberField.discr k).natAbs.factorization.support
  have hPprime : ∀ q ∈ P, q.Prime := by
    intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp h
      exact pof_prime k Ω A.1 (hS A.1 A.2)
    · rw [Nat.support_factorization] at h
      exact (Nat.mem_primeFactors.mp h).1
  obtain ⟨C, hC⟩ := abs_discr_le_primeSet_clean Ω P hPprime (n * Module.finrank ℚ k)
  refine ⟨C, ?_⟩
  intro L hL hdeg hram h
  have hMdeg : Module.finrank ℚ ↥(L.restrictScalars ℚ) ≤ n * Module.finrank ℚ k := by
    have h1 : Module.finrank ℚ ↥(L.restrictScalars ℚ) = Module.finrank ℚ ↥L := rfl
    rw [h1, Nat.mul_comm n]
    calc Module.finrank ℚ ↥L = Module.finrank ℚ k * Module.finrank k ↥L :=
          (Module.finrank_mul_finrank ℚ k ↥L).symm
      _ ≤ Module.finrank ℚ k * n := Nat.mul_le_mul_left _ hdeg
  have hMprime : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace ℚ B →
      SSGRoute.IsRamifiedIn ℚ (L.restrictScalars ℚ) B → ∃ q ∈ P, B.valuation (q : Ω) < 1 := by
    intro B hBq hBram
    obtain ⟨σ, hσI, hσne⟩ := hBram
    by_cases hσfix : ∀ x : k, σ (algebraMap k Ω x) = algebraMap k Ω x
    · have hBk : SSGRoute.IsFinPlace k B := kview_base_ne_top k Ω B hBq
      have hramL : SSGRoute.IsRamifiedIn k L B :=
        isRamifiedIn_base_of_isRamifiedIn_rat_fixing k Ω L B σ hσI hσfix hσne
      obtain ⟨A, hA, hconj⟩ := hram B hBk hramL
      refine ⟨pof k Ω A (hS A hA), ?_, ?_⟩
      · exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach _ _, rfl⟩)
      · exact valuation_lt_one_of_isConjPlace k Ω hconj (pof_valuation_lt_one k Ω A (hS A hA))
    · have hramk : SSGRoute.IsRamifiedIn ℚ (kview k Ω) B :=
        ⟨σ, hσI, fun hmem => hσfix ((mem_kview_fixingSubgroup_iff k Ω σ).mp hmem)⟩
      obtain ⟨p, hp, hpv, hpdvd⟩ :=
        prime_dvd_discr_of_isRamifiedIn_algebraicClosure Ω (kview k Ω) B hBq hramk
      have hdisc : NumberField.discr k = NumberField.discr ↥(kview k Ω) :=
        NumberField.discr_eq_discr_of_algEquiv k (kviewEquiv k Ω)
      have hpdvd' : p ∣ (NumberField.discr k).natAbs := by
        rw [hdisc]
        exact hpdvd
      have hBk : SSGRoute.IsFinPlace k B := kview_base_ne_top k Ω B hBq
      have hqeq : p = pof k Ω B hBk :=
        eq_of_prime_valuation_lt_one Ω B hp (pof_prime k Ω B hBk) hpv
          (pof_valuation_lt_one k Ω B hBk)
      have hPmem : pof k Ω B hBk ∈ (NumberField.discr k).natAbs.factorization.support := by
        rw [← hqeq, Nat.support_factorization]
        exact Nat.mem_primeFactors.mpr ⟨hp, hpdvd',
          Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero k)⟩
      exact ⟨pof k Ω B hBk, Finset.mem_union_right _ hPmem, pof_valuation_lt_one k Ω B hBk⟩
  exact hC ⟨L.restrictScalars ℚ, h⟩ hMdeg hMprime

/-- **Hermite–Minkowski: finitely many extensions of bounded degree unramified outside a finite
place set** — the `finiteHM.finite_of_bddDegree_unamifiedOutside_proved` statement with the
axiom-clean discriminant bound. -/
theorem finite_of_bddDegree_unamifiedOutside_clean
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (S : Finset (ValuationSubring Ω)) (hS : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (n : ℕ) :
    {L : {F : IntermediateField k Ω // FiniteDimensional k F} |
      haveI : FiniteDimensional k L := L.2
      Module.finrank k L ≤ n ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → SSGRoute.IsRamifiedIn k L B →
        ∃ A ∈ S, SSGRoute.IsConjPlace k A B)}.Finite := by
  classical
  haveI hchar : CharZero Ω := charZero_of_inj_zero (fun m hm => by
    have h1 : algebraMap k Ω (m : k) = 0 := by rw [map_natCast]; exact hm
    have h2 : (m : k) = (0 : k) := RingHom.injective (algebraMap k Ω) (by simpa using h1)
    exact CharZero.cast_injective (R := k) (by simpa using h2))
  obtain ⟨C, hC⟩ := exists_absDiscr_le_clean k Ω S hS n
  have hψinj : Function.Injective
      (fun L : {F : IntermediateField k Ω // FiniteDimensional k F} =>
        (⟨L.1.restrictScalars ℚ, by
          haveI : FiniteDimensional k L.1 := L.2
          exact FiniteDimensional.trans ℚ k ↥L.1⟩ :
          {F : IntermediateField ℚ Ω // FiniteDimensional ℚ F})) := by
    intro L₁ L₂ h
    have h1 : L₁.1.restrictScalars ℚ = L₂.1.restrictScalars ℚ := congrArg Subtype.val h
    have h2 : L₁.1 ≤ L₂.1 := (IntermediateField.restrictScalars_le_iff ℚ).mp (le_of_eq h1)
    have h3 : L₂.1 ≤ L₁.1 := (IntermediateField.restrictScalars_le_iff ℚ).mp (le_of_eq h1.symm)
    exact Subtype.ext (le_antisymm h2 h3)
  refine Set.Finite.of_finite_image ?_ hψinj.injOn
  refine (NumberField.finite_of_discr_bdd Ω C).subset ?_
  rintro K ⟨L, ⟨hdeg, hunr⟩, hLK⟩
  haveI : FiniteDimensional k L.1 := L.2
  rw [← hLK]
  exact hC L.1 hdeg hunr (FiniteDimensional.trans ℚ k ↥L.1)

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
