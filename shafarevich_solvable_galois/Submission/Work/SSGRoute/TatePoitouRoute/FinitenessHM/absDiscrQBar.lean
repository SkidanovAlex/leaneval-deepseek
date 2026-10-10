import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.differentIdeal_count_le_clean_bound
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.isRamifiedIn_comap_algEquiv_proved
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.isRamifiedIn_of_dvd_discr_natAbs_proved
import Submission.Work.SSGRoute.placePrime_eq_of_val_lt_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A uniform bound for the discriminant of a field of bounded degree unramified outside `S`
(clean, axiom-free copy with the arithmetic inputs re-pointed)

This is the *arithmetic heart* of the Hermite–Minkowski finiteness statement: for a finite set `S`
of finite places of `ℚ̄` and a bound `n` on the degree, there is `C` with `|disc K| ≤ C` for every
number field `K ⊆ ℚ̄` of degree `≤ n` all of whose ramified finite places are conjugate to places
in `S`.

**Why this file exists.**  The statement and its proof are those of
`Submission/Work/SSGRoute/Finiteness/abs_discr_le_of_bddDegree_unramifiedOutside.lean` (the
`Finiteness` lane).  That file is itself `sorry`-free, but it `import`s three *statement stubs*
carrying the lane's remaining `sorry`s
(`Finiteness/differentIdeal_count_le.lean`, `Finiteness/isRamifiedIn_of_dvd_discr_natAbs.lean`,
`Finiteness/isRamifiedIn_comap_algEquiv.lean`), so every consumer of it is `sorryAx`-tainted.  This
copy imports `sorry`-free, axiom-clean proofs of those three inputs instead:

* `Work.SSGRoute.TatePoitouRoute.FinitenessHM.differentIdeal_count_le_proved`
  (the classical bound `v_P(𝔡_{K/ℚ}) ≤ e·(1 + e·v_p(e))`),
* `Work.SSGRoute.TatePoitouRoute.FinitenessHM.isRamifiedIn_of_dvd_discr_natAbs_proved`
  (a prime dividing `disc K` is ramified somewhere),
* `Work.SSGRoute.TatePoitouRoute.FinitenessHM.isRamifiedIn_comap_algEquiv_proved`
  (transport of ramification along `A ≃ₐ[ℚ] ℚ̄`),

so that the present file and its consumer `finite_of_bddDegree_unramifiedOutside_proved` are
verified rather than tainted.  The textbook steps are the counting of the primes above a rational
prime (at most `[K : ℚ]` of them, each of inertia degree at most `[K : ℚ]`) and the confinement of
the support of `disc K` to the primes below `S`.
-/

open NumberField UniqueFactorizationMonoid
open scoped NumberField
open scoped Pointwise

set_option linter.style.haveILetI false

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

/-- A crude uniform bound for the exponent of a rational prime in the discriminant of a number
field of degree `n`: it only depends on `n`. -/
def expBound (n : ℕ) : ℕ := n * ((n * (1 + n * n)) * n)

private lemma expBound_mono {a b : ℕ} (hab : a ≤ b) : expBound a ≤ expBound b := by
  unfold expBound
  gcongr

section Counting

/-- **The exponent of a rational prime in the discriminant is bounded by a function of the
degree.** -/
theorem padicValNat_discr_le {K : Type*} [Field K] [NumberField K] (q : ℕ) [Fact q.Prime]
    (hdiff : ∀ (P : Ideal (𝓞 K)), P.IsPrime → P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) →
      (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ≤
        P.ramificationIdx ℤ * (1 + P.ramificationIdx ℤ * padicValNat q (P.ramificationIdx ℤ))) :
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
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter (fun P => P.LiesOver pp) with hs
  have hne : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
  rw [Commons.NumberTheory.NumberField.discr_padicValNat_eq_sum_over_p_count_mul_inertiaDeg q]
  change (∑ P ∈ s, (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ) ≤
    expBound n
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
      (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ ≤
        (n * (1 + n * n)) * n := by
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
    have he : P.ramificationIdx ℤ ≤ n := by
      have h1 : Ideal.ramificationIdx' pp P ≤ Module.finrank ℚ K :=
        Ideal.ramificationIdx_le_finrank (𝓞 K) ℚ K P
      have h2 : Ideal.ramificationIdx' pp P = P.ramificationIdx ℤ :=
        Ideal.ramificationIdx'_eq_ramificationIdx (p := pp) (q := P) hpp0
      rw [h2] at h1
      rwa [hn]
    have hf : P.inertiaDeg ℤ ≤ n := by
      have h1 : Ideal.inertiaDeg' pp P ≤ Module.finrank ℚ K :=
        Ideal.inertiaDeg_le_finrank (𝓞 K) ℚ K P hpp0
      have h2 : Ideal.inertiaDeg' pp P = P.inertiaDeg ℤ :=
        Ideal.inertiaDeg'_eq_inertiaDeg (p := pp) (P := P)
      rw [h2] at h1
      rwa [hn]
    have hv : padicValNat q (P.ramificationIdx ℤ) ≤ n := by
      rcases Nat.eq_zero_or_pos (P.ramificationIdx ℤ) with h0 | h0
      · simp [h0]
      · have h1 : q ^ padicValNat q (P.ramificationIdx ℤ) ∣ P.ramificationIdx ℤ :=
          pow_padicValNat_dvd
        have h2 : q ^ padicValNat q (P.ramificationIdx ℤ) ≤ n :=
          le_trans (Nat.le_of_dvd h0 h1) he
        have h3 : n < q ^ n :=
          lt_of_lt_of_le Nat.lt_two_pow_self
            (Nat.pow_le_pow_left (Fact.out : q.Prime).two_le n)
        have h4 : q ^ padicValNat q (P.ramificationIdx ℤ) < q ^ n := lt_of_le_of_lt h2 h3
        exact le_of_lt ((Nat.pow_lt_pow_iff_right (Fact.out : q.Prime).one_lt).mp h4)
    calc (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ
        ≤ (P.ramificationIdx ℤ * (1 + P.ramificationIdx ℤ *
              padicValNat q (P.ramificationIdx ℤ))) * P.inertiaDeg ℤ := by
          exact Nat.mul_le_mul_right _ (hdiff P hprime hlie)
      _ ≤ (n * (1 + n * n)) * n := by
          refine Nat.mul_le_mul ?_ hf
          exact Nat.mul_le_mul he (Nat.add_le_add_left (Nat.mul_le_mul he hv) 1)
  calc ∑ P ∈ s, (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ
      ≤ s.card • ((n * (1 + n * n)) * n) := Finset.sum_le_card_nsmul s _ _ hterm
    _ = s.card * ((n * (1 + n * n)) * n) := by rw [nsmul_eq_mul, Nat.cast_id]
    _ ≤ n * ((n * (1 + n * n)) * n) := Nat.mul_le_mul_right _ hcard
    _ = expBound n := rfl

end Counting

section QBar

/-- The rational primes below the finite places in `S`. -/
noncomputable def primesBelow (S : Finset (ValuationSubring SSGRoute.QBar))
    (hS : ∀ A' ∈ S, SSGRoute.IsFinPlace ℚ A') : Finset ℕ :=
  S.attach.image (fun V => (Work.SSGRoute.placePrime V.1 (hS V.1 V.2)).1)

/-- **The discriminant bound over `ℚ̄`.** -/
theorem abs_discr_le_QBar (S : Finset (ValuationSubring SSGRoute.QBar))
    (hS : ∀ A' ∈ S, SSGRoute.IsFinPlace ℚ A') (n : ℕ) :
    ∀ (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K],
      Module.finrank ℚ K ≤ n →
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
        SSGRoute.IsRamifiedIn ℚ K B → ∃ A' ∈ S, SSGRoute.IsConjPlace ℚ A' B) →
      (NumberField.discr K).natAbs ≤ ∏ p ∈ primesBelow S hS, p ^ expBound n := by
  classical
  intro K hK hdeg hram
  haveI : NumberField K := NumberField.of_module_finite ℚ K
  set N : ℕ := (NumberField.discr K).natAbs with hN
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)
  have hsupp : ∀ q : ℕ, q.Prime → q ∉ primesBelow S hS → padicValNat q N = 0 := by
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
    obtain ⟨A', hA', hconj⟩ := hram B hBfin hBram
    obtain ⟨τ, hτ⟩ := hconj
    have hAval : A'.valuation (q : SSGRoute.QBar) < 1 := by
      have h1 : (A'.comap (algebraMap ℚ SSGRoute.QBar)).valuation (q : ℚ) < 1 := by
        rw [← Work.SSGRoute.comap_algebraMap_smul A' τ, hτ]
        exact (Work.SSGRoute.comap_valuation_lt_one_iff B (q : ℚ)).mpr (by simpa using hBval)
      have h2 := (Work.SSGRoute.comap_valuation_lt_one_iff A' (q : ℚ)).mp h1
      simpa using h2
    have hpp : Work.SSGRoute.placePrime A' (hS A' hA') = ⟨q, hq⟩ :=
      Work.SSGRoute.placePrime_eq_of_val_lt_one q A' (hS A' hA') hAval
    refine hqmem (Finset.mem_image.mpr ⟨⟨A', hA'⟩, Finset.mem_attach _ _, ?_⟩)
    show (Work.SSGRoute.placePrime A' (hS A' hA')).1 = q
    rw [hpp]
  have h1 : N.factorization.support ⊆ primesBelow S hS := by
    intro q hq
    rw [Finsupp.mem_support_iff] at hq
    have hqprime : q.Prime := by
      by_contra hq'
      exact hq (Nat.factorization_eq_zero_of_not_prime N hq')
    by_contra hqmem
    exact hq (by rw [Nat.factorization_def N hqprime]; exact hsupp q hqprime hqmem)
  have hprime_of : ∀ q ∈ primesBelow S hS, q.Prime := by
    intro q hq
    rw [primesBelow, Finset.mem_image] at hq
    obtain ⟨V, _, rfl⟩ := hq
    exact (Work.SSGRoute.placePrime V.1 (hS V.1 V.2)).2
  have hmain : N = ∏ p ∈ primesBelow S hS, p ^ padicValNat p N := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
    rw [Finsupp.prod]
    refine (Finset.prod_subset h1 ?_).trans ?_
    · intro q _ hqnot
      rw [Finsupp.notMem_support_iff.mp hqnot, pow_zero]
    · exact Finset.prod_congr rfl (fun q hq => by
        rw [Nat.factorization_def N (hprime_of q hq)])
  calc N = ∏ p ∈ primesBelow S hS, p ^ padicValNat p N := hmain
    _ ≤ ∏ p ∈ primesBelow S hS, p ^ expBound n := by
        refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) (fun p hp => ?_)
        have hp' := hprime_of p hp
        haveI : Fact p.Prime := ⟨hp'⟩
        refine Nat.pow_le_pow_right (Nat.Prime.pos hp') ?_
        refine le_trans (padicValNat_discr_le p
          (fun P hP hlie => differentIdeal_count_le_clean_bound p P hP hlie)) ?_
        exact expBound_mono hdeg

end QBar

section Transfer

/-- **Finiteness of a place is preserved by pulling back along a `ℚ`-algebra homomorphism.** -/
private lemma isFinPlace_comap_iff {A Ω : Type} [Field A] [Field Ω] [Algebra ℚ A] [Algebra ℚ Ω]
    (f : A →+* Ω) (hf : f.comp (algebraMap ℚ A) = algebraMap ℚ Ω) (B : ValuationSubring Ω) :
    SSGRoute.IsFinPlace ℚ (B.comap f) ↔ SSGRoute.IsFinPlace ℚ B := by
  simp only [SSGRoute.IsFinPlace, ValuationSubring.comap_comap, hf]

variable {A : Type} [Field A] [Algebra ℚ A]

private lemma isFinPlace_pushforward (σ : A ≃ₐ[ℚ] SSGRoute.QBar) (V : ValuationSubring A) :
    SSGRoute.IsFinPlace ℚ (V.comap (σ.symm : SSGRoute.QBar →+* A)) ↔
      SSGRoute.IsFinPlace ℚ V := by
  have hcomp : ((σ.symm : SSGRoute.QBar →+* A)).comp (algebraMap ℚ SSGRoute.QBar) =
      algebraMap ℚ A := by
    ext r
    exact σ.symm.commutes r
  exact isFinPlace_comap_iff (σ.symm : SSGRoute.QBar →+* A) hcomp V

private lemma isFinPlace_pullback (σ : A ≃ₐ[ℚ] SSGRoute.QBar) (B : ValuationSubring SSGRoute.QBar) :
    SSGRoute.IsFinPlace ℚ (B.comap (σ : A →+* SSGRoute.QBar)) ↔ SSGRoute.IsFinPlace ℚ B := by
  have hcomp : ((σ : A →+* SSGRoute.QBar)).comp (algebraMap ℚ A) = algebraMap ℚ SSGRoute.QBar := by
    ext r
    exact σ.commutes r
  exact isFinPlace_comap_iff (σ : A →+* SSGRoute.QBar) hcomp B

/-- **Conjugacy of places is preserved by an isomorphism.** -/
private lemma isConjPlace_pushforward (σ : A ≃ₐ[ℚ] SSGRoute.QBar) (V W : ValuationSubring A)
    (h : SSGRoute.IsConjPlace ℚ V W) :
    SSGRoute.IsConjPlace ℚ (V.comap (σ.symm : SSGRoute.QBar →+* A))
      (W.comap (σ.symm : SSGRoute.QBar →+* A)) := by
  obtain ⟨τ, hτ⟩ := h
  have hcoe : ∀ y : SSGRoute.QBar,
      ((σ.symm.trans (τ.trans σ)) : SSGRoute.QBar → SSGRoute.QBar) y = σ (τ (σ.symm y)) := by
    intro y
    rfl
  refine ⟨σ.symm.trans (τ.trans σ), ?_⟩
  have hsmul : (σ.symm.trans (τ.trans σ)) • (V.comap (σ.symm : SSGRoute.QBar →+* A)) =
      (τ • V).comap (σ.symm : SSGRoute.QBar →+* A) := by
    ext x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, hsx⟩
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_smul_pointwise_iff_exists]
      refine ⟨σ.symm s, hs, ?_⟩
      rw [← hsx]
      show τ (σ.symm s) = σ.symm (σ (τ (σ.symm s)))
      rw [σ.symm_apply_apply]
    · intro hx
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_smul_pointwise_iff_exists] at hx
      obtain ⟨v, hv, hvx⟩ := hx
      refine ⟨σ v, ?_, ?_⟩
      · rw [ValuationSubring.mem_comap]
        simpa using hv
      · have h2 : σ (τ • v) = x := by
          rw [hvx]
          exact AlgEquiv.apply_symm_apply σ x
        have h3 : (σ.symm.trans (τ.trans σ)) (σ v) = σ (τ • v) := by
          rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
          rfl
        show (σ.symm.trans (τ.trans σ)) (σ v) = x
        rw [h3, h2]
  rw [hsmul, hτ]

end Transfer

/-- **A uniform bound for the discriminant of a field of bounded degree unramified outside `S`.** -/
theorem abs_discr_le_of_bddDegree_unramifiedOutside
    (A : Type) [Field A] [CharZero A] [IsAlgClosure ℚ A]
    (S : Finset (ValuationSubring A)) (hS : ∀ A' ∈ S, SSGRoute.IsFinPlace ℚ A') (n : ℕ) :
    ∃ C : ℕ, ∀ (K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F}),
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.2
      Module.finrank ℚ K ≤ n →
      (∀ B : ValuationSubring A, SSGRoute.IsFinPlace ℚ B → SSGRoute.IsRamifiedIn ℚ K B →
        ∃ A' ∈ S, SSGRoute.IsConjPlace ℚ A' B) →
      |NumberField.discr K| ≤ C := by
  classical
  obtain ⟨σ⟩ : Nonempty (A ≃ₐ[ℚ] SSGRoute.QBar) := ⟨IsAlgClosure.equiv ℚ A SSGRoute.QBar⟩
  let S' : Finset (ValuationSubring SSGRoute.QBar) :=
    S.attach.image (fun V => V.1.comap (σ.symm : SSGRoute.QBar →+* A))
  have hS' : ∀ V ∈ S', SSGRoute.IsFinPlace ℚ V := by
    intro V hV
    rw [Finset.mem_image] at hV
    obtain ⟨W, _, rfl⟩ := hV
    exact (isFinPlace_pushforward σ W.1).2 (hS W.1 W.2)
  refine ⟨∏ p ∈ primesBelow S' hS', p ^ expBound n, ?_⟩
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
      SSGRoute.IsRamifiedIn ℚ K' B' → ∃ V ∈ S', SSGRoute.IsConjPlace ℚ V B' := by
    intro B' hB'fin hB'ram
    have hBfin : SSGRoute.IsFinPlace ℚ (B'.comap (σ : A →+* SSGRoute.QBar)) :=
      (isFinPlace_pullback σ B').mpr hB'fin
    have hBram : SSGRoute.IsRamifiedIn ℚ K.1 (B'.comap (σ : A →+* SSGRoute.QBar)) :=
      (isRamifiedIn_comap_algEquiv_proved A σ K.1 B').mpr hB'ram
    obtain ⟨V₀, hV₀, hconj⟩ := hram (B'.comap (σ : A →+* SSGRoute.QBar)) hBfin hBram
    refine ⟨V₀.comap (σ.symm : SSGRoute.QBar →+* A), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨V₀, hV₀⟩, Finset.mem_attach _ _, rfl⟩
    · have h1 := isConjPlace_pushforward σ V₀ (B'.comap (σ : A →+* SSGRoute.QBar)) hconj
      rw [ValuationSubring.comap_comap,
        show ((σ : A →+* SSGRoute.QBar)).comp (σ.symm : SSGRoute.QBar →+* A) =
          RingHom.id SSGRoute.QBar from by ext y; simp] at h1
      have hid : B'.comap (RingHom.id SSGRoute.QBar) = B' := by ext x; rfl
      rwa [hid] at h1
  have hcore := abs_discr_le_QBar S' hS' n K' hdeg' hram'
  have hdisc : NumberField.discr K.1 = NumberField.discr K' :=
    NumberField.discr_eq_discr_of_algEquiv ↥K.1 (IntermediateField.equivMap K.1 σ.toAlgHom)
  rw [hdisc]
  refine le_trans (le_of_eq (Int.natCast_natAbs (NumberField.discr K')).symm) ?_
  exact_mod_cast hcore

section PrimeLevel

/-- **Comparison of the `(-).valuation (·) < 1` condition along an arbitrary ring hom.**  This is
`Work.SSGRoute.comap_valuation_lt_one_iff` with the `algebraMap` replaced by a general `f`. -/
theorem comap_valuation_lt_one_iff' {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (B : ValuationSubring L) (x : K) :
    (B.comap f).valuation x < 1 ↔ B.valuation (f x) < 1 := by
  have hsub : (B.comap f).valuation.valuationSubring =
      (B.valuation.comap f).valuationSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    ext y
    simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      ValuationSubring.valuation_le_one_iff, Valuation.comap_apply]
  have heq : (B.comap f).valuation.IsEquiv (B.valuation.comap f) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub
  rw [Valuation.IsEquiv.lt_one_iff_lt_one heq]
  rfl

/-- **The discriminant bound over `ℚ̄`, in the form in which the ramification hypothesis is
imposed only through the *rational primes* below the ramified places** (a strictly weaker
hypothesis than `abs_discr_le_QBar`'s conjugacy-to-a-place-in-`S`). -/
theorem abs_discr_le_QBar_primeSet (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (n : ℕ) :
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
          (fun P' hP' hlie => differentIdeal_count_le_clean_bound p P' hP' hlie)) ?_
        exact expBound_mono hdeg

/-- **A uniform bound for the discriminant, with the ramification hypothesis imposed through the
rational primes below the ramified places.**  This is the form the general-base-field reduction
needs: it never asks for a place of `A` over a given rational prime. -/
theorem abs_discr_le_primeSet (A : Type) [Field A] [CharZero A] [IsAlgClosure ℚ A]
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
      (isFinPlace_pullback σ B').mpr hB'fin
    have hBram : SSGRoute.IsRamifiedIn ℚ K.1 (B'.comap (σ : A →+* SSGRoute.QBar)) :=
      (isRamifiedIn_comap_algEquiv_proved A σ K.1 B').mpr hB'ram
    obtain ⟨q, hqP, hqval⟩ := hram (B'.comap (σ : A →+* SSGRoute.QBar)) hBfin hBram
    refine ⟨q, hqP, ?_⟩
    have hσq : (σ : A →+* SSGRoute.QBar) (q : A) = (q : SSGRoute.QBar) := map_natCast _ _
    rw [← hσq, ← comap_valuation_lt_one_iff' (σ : A →+* SSGRoute.QBar) B' (q : A)]
    exact hqval
  have hcore := abs_discr_le_QBar_primeSet P hP n K' hdeg' hram'
  have hdisc : NumberField.discr K.1 = NumberField.discr K' :=
    NumberField.discr_eq_discr_of_algEquiv ↥K.1 (IntermediateField.equivMap K.1 σ.toAlgHom)
  rw [hdisc]
  refine le_trans (le_of_eq (Int.natCast_natAbs (NumberField.discr K')).symm) ?_
  exact_mod_cast hcore

/-- **Hermite–Minkowski, prime form**: over an algebraic closure of `ℚ`, there are only finitely
many finite extensions of `ℚ` of degree `≤ n` all of whose ramified places lie over one of the
primes in `P`. -/
theorem finite_of_bddDegree_unamifiedOutside_primeSet
    (A : Type) [Field A] [CharZero A] [IsAlgClosure ℚ A]
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (n : ℕ) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI : FiniteDimensional ℚ K := K.2
      Module.finrank ℚ K ≤ n ∧
      (∀ B : ValuationSubring A, SSGRoute.IsFinPlace ℚ B → SSGRoute.IsRamifiedIn ℚ K B →
        ∃ q ∈ P, B.valuation (q : A) < 1)}.Finite := by
  classical
  obtain ⟨C, hC⟩ := abs_discr_le_primeSet A P hP n
  refine (NumberField.finite_of_discr_bdd A C).subset ?_
  rintro K ⟨hdeg, hunr⟩
  exact hC K hdeg hunr

end PrimeLevel

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
