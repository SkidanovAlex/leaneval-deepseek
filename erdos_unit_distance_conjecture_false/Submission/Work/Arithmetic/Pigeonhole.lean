import Submission.Work.Arithmetic.CMDefs
import Submission.Work.Arithmetic.PigeonholeAux.fiber
import Submission.Work.Arithmetic.PigeonholeAux.dvd_span_sq
import Submission.Work.Arithmetic.PigeonholeAux.uOf_mul_conj
import Submission.Work.Arithmetic.PigeonholeAux.span_singleton_uOf

/-!
# The class-group pigeonhole (Proposition 2.2 of the paper)

Given a CM field `K`, distinct non-conjugate prime ideals `P 1, …, P m` each containing a
rational prime dividing `Q`, we produce `≥ 2^m / h(K)` elements `u ∈ K` with `u c(u) = 1`
and `Q² u ∈ 𝓞 K`, where `c` is complex conjugation and `h(K)` the class number.

The proof follows the paper: the `2^m` ideals `A_ε = ∏_{ε_i=1} P_i ∏_{ε_i=0} c P_i`
occupy only `h(K)` ideal classes, so one class fibre has `≥ 2^m/h(K)` elements; ratios of
generators of `A_ε A_η^{-1}` give the elements `u_ε`, whose valuations at the `P_i`
distinguish them.
-/

namespace Work.Arithmetic

open scoped nonZeroDivisors
open NumberField

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- A nonzero prime ideal of `𝓞 K` is maximal, so it cannot properly contain a prime. -/
lemma eq_of_isPrime_le {I J : Ideal (𝓞 K)} (hI : I.IsPrime) (hI0 : I ≠ ⊥) (hJ : J.IsPrime)
    (h : I ≤ J) : I = J :=
  (hI.isMaximal hI0).eq_of_le hJ.ne_top h

/-- Which primes `P s` divide `A_ε A'_{ε'}`: exactly those with `ε s = true` or `ε' s = false`. -/
theorem le_ASet_mul_ASet'_iff (m : ℕ) (P : Fin m → Ideal (𝓞 K))
    (hP : ∀ i, (P i).IsPrime) (hPne : ∀ i j, i ≠ j → P i ≠ P j)
    (hconj : ∀ i j, conjI (P i) ≠ P j) (hnb : ∀ i, P i ≠ ⊥)
    (s : Fin m) (ε ε' : Fin m → Bool) :
    ASet m P ε * ASet' m P ε' ≤ P s ↔ (ε s = true ∨ ε' s = false) := by
  have hprime : (P s).IsPrime := hP s
  rw [ASet_mul_ASet'_swap, Ideal.IsPrime.prod_le hprime]
  constructor
  · rintro ⟨i, -, hi⟩
    rw [Ideal.IsPrime.mul_le hprime] at hi
    have key1 : (if ε i then P i else conjI (P i)) ≤ P s → ε i = true ∧ i = s := by
      intro h1
      by_cases he : ε i = true
      · refine ⟨he, ?_⟩
        rw [ite_eq_left he] at h1
        by_contra hne
        exact hPne i s hne (eq_of_isPrime_le (hP i) (hnb i) hprime h1)
      · rw [ite_eq_right he] at h1
        exact absurd (eq_of_isPrime_le (conjI_prime (hP i)) (conjI_ne_bot (hnb i)) hprime h1)
          (hconj i s)
    have key2 : (if ε' i then conjI (P i) else P i) ≤ P s → ε' i = false ∧ i = s := by
      intro h1
      by_cases he : ε' i = true
      · rw [ite_eq_left he] at h1
        exact absurd (eq_of_isPrime_le (conjI_prime (hP i)) (conjI_ne_bot (hnb i)) hprime h1)
          (hconj i s)
      · rw [ite_eq_right he] at h1
        refine ⟨?_, ?_⟩
        · simp [he]
        · by_contra hne
          exact hPne i s hne (eq_of_isPrime_le (hP i) (hnb i) hprime h1)
    rcases hi with hi | hi
    · obtain ⟨he, his⟩ := key1 hi
      exact Or.inl (by rw [← his, he])
    · obtain ⟨he, his⟩ := key2 hi
      exact Or.inr (by rw [← his, he])
  · rintro (h | h)
    · refine ⟨s, Finset.mem_univ _, ?_⟩
      rw [ite_eq_left h]
      exact Ideal.mul_le_left
    · refine ⟨s, Finset.mem_univ _, ?_⟩
      rw [ite_eq_right (show ¬(ε' s = true) by simp [h])]
      exact Ideal.mul_le_right

/-- The map `ε ↦ A_ε A'_{ε'}` is injective: if `A_ε A'_{ε'} = A_{ε'} A'_ε` then `ε = ε'`. -/
theorem eq_of_ASet_mul_eq (m : ℕ) (P : Fin m → Ideal (𝓞 K))
    (hP : ∀ i, (P i).IsPrime) (hPne : ∀ i j, i ≠ j → P i ≠ P j)
    (hconj : ∀ i j, conjI (P i) ≠ P j) (hnb : ∀ i, P i ≠ ⊥)
    (ε ε' : Fin m → Bool)
    (h : ASet m P ε * ASet' m P ε' = ASet m P ε' * ASet' m P ε) : ε = ε' := by
  funext s
  have h1 := le_ASet_mul_ASet'_iff m P hP hPne hconj hnb s ε ε'
  have h2 := le_ASet_mul_ASet'_iff m P hP hPne hconj hnb s ε' ε
  have hiff : ASet m P ε * ASet' m P ε' ≤ P s ↔ ASet m P ε' * ASet' m P ε ≤ P s := by
    rw [h]
  rw [h1, h2] at hiff
  revert hiff
  cases ε s <;> cases ε' s <;> simp

/-- From the fractional-ideal identity `(u_ε) = A_ε A'_η (A_η A'_ε)⁻¹` for the same element
`u` we may conclude the ideal identity `A_ε A'_{ε'} = A_{ε'} A'_ε`. -/
theorem ASet_mul_eq_of_fractional_eq (m : ℕ) (P : Fin m → Ideal (𝓞 K)) (η ε ε' : Fin m → Bool)
    (hη : ASet m P η ≠ ⊥) (hε : ASet m P ε ≠ ⊥) (hε' : ASet m P ε' ≠ ⊥)
    (h : ((ASet m P ε : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          (((ASet' m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
          ((((ASet m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
            (((ASet' m P ε : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)))⁻¹ =
        ((ASet m P ε' : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          (((ASet' m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
          ((((ASet m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
            (((ASet' m P ε' : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)))⁻¹) :
    ASet m P ε * ASet' m P ε' = ASet m P ε' * ASet' m P ε := by
  set Aε : FractionalIdeal (𝓞 K)⁰ K := ((ASet m P ε : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    with hAε
  set Aη : FractionalIdeal (𝓞 K)⁰ K := ((ASet m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    with hAη
  set Aε' : FractionalIdeal (𝓞 K)⁰ K := ((ASet m P ε' : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    with hAε'
  set A'η : FractionalIdeal (𝓞 K)⁰ K := ((ASet' m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    with hA'η
  set A'ε : FractionalIdeal (𝓞 K)⁰ K := ((ASet' m P ε : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    with hA'ε
  set A'ε' : FractionalIdeal (𝓞 K)⁰ K :=
    ((ASet' m P ε' : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) with hA'ε'
  have hAη0 : Aη ≠ 0 := by rw [hAη]; exact FractionalIdeal.coeIdeal_ne_zero.mpr hη
  have hAε0 : Aε ≠ 0 := by rw [hAε]; exact FractionalIdeal.coeIdeal_ne_zero.mpr hε
  have hAε'0 : Aε' ≠ 0 := by rw [hAε']; exact FractionalIdeal.coeIdeal_ne_zero.mpr hε'
  have hA'η0 : A'η ≠ 0 := by
    rw [hA'η, ← conjI_ASet]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr (conjI_ne_bot hη)
  have hA'ε0 : A'ε ≠ 0 := by
    rw [hA'ε, ← conjI_ASet]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr (conjI_ne_bot hε)
  have hA'ε'0 : A'ε' ≠ 0 := by
    rw [hA'ε', ← conjI_ASet]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr (conjI_ne_bot hε')
  have h1 : (Aε * A'η) / (Aη * A'ε) = (Aε' * A'η) / (Aη * A'ε') := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact h
  have h2 : Aε * A'η * (Aη * A'ε') = Aε' * A'η * (Aη * A'ε) :=
    (div_eq_div_iff (mul_ne_zero hAη0 hA'ε0) (mul_ne_zero hAη0 hA'ε'0)).mp h1
  have h3 : Aε * A'ε' = Aε' * A'ε := by
    have key : (A'η * Aη) * (Aε * A'ε') = (A'η * Aη) * (Aε' * A'ε) := by
      calc (A'η * Aη) * (Aε * A'ε') = Aε * A'η * (Aη * A'ε') := by ac_rfl
        _ = Aε' * A'η * (Aη * A'ε) := h2
        _ = (A'η * Aη) * (Aε' * A'ε) := by ac_rfl
    exact mul_left_cancel₀ (mul_ne_zero hA'η0 hAη0) key
  rw [hAε, hAε', hA'ε, hA'ε'] at h3
  rw [← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul] at h3
  exact FractionalIdeal.coeIdeal_inj.mp h3


/-- `Q² u` is an algebraic integer, i.e. `u ∈ Q⁻² 𝓞 K`. -/
theorem uOf_integral (m : ℕ) (P : Fin m → Ideal (𝓞 K))
    (hP : ∀ i, (P i).IsPrime) (hPne : ∀ i j, i ≠ j → P i ≠ P j)
    (hconj : ∀ i j, conjI (P i) ≠ P j)
    (Q : ℕ) (hQ : ∀ i, ∃ p : ℕ, p ∣ Q ∧ Nat.Prime p ∧ Ideal.span {(p : 𝓞 K)} ≤ P i)
    (η ε : Fin m → Bool) (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : Ideal.span {x} * ASet m P ε = Ideal.span {y} * ASet m P η) :
    ∃ w : 𝓞 K, (w : K) = (Q : K) ^ 2 * uOf x y := by
  have hnb : ∀ i, P i ≠ ⊥ := by
    intro i
    obtain ⟨p, -, hp, hpP⟩ := hQ i
    intro hbot
    have hmem : (p : 𝓞 K) ∈ (⊥ : Ideal (𝓞 K)) := hbot ▸ hpP (Ideal.mem_span_singleton_self _)
    have hp0 : (p : 𝓞 K) = 0 := by simpa using hmem
    exact hp.ne_zero (Nat.cast_eq_zero.mp hp0)
  have hε : ASet m P ε ≠ ⊥ := ASet_ne_bot m P hnb ε
  have hη : ASet m P η ≠ ⊥ := ASet_ne_bot m P hnb η
  have h8 := PigeonholeAux.span_singleton_uOf m P η ε hε hη x y hx hy hxy
  have hdvd : Ideal.span {((Q : 𝓞 K) ^ 2)} ≤ ASet m P η * ASet' m P ε :=
    Ideal.dvd_iff_le.mp (PigeonholeAux.dvd_span_sq m P hP hPne hconj Q hQ η ε)
  have hstep : Ideal.span {((Q : 𝓞 K) ^ 2)} * ASet m P ε * ASet' m P η
      ≤ Ideal.span {((Q : 𝓞 K) ^ 2)} :=
    le_trans Ideal.mul_le_left Ideal.mul_le_left
  have hineq : Ideal.span {((Q : 𝓞 K) ^ 2)} * ASet m P ε * ASet' m P η
      ≤ ASet m P η * ASet' m P ε := le_trans hstep hdvd
  have hmain := (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hineq
  simp only [FractionalIdeal.coeIdeal_mul] at hmain
  have hQspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((Q : K) ^ 2)
      = ((Ideal.span {((Q : 𝓞 K) ^ 2)} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton]
    refine congrArg (FractionalIdeal.spanSingleton (𝓞 K)⁰) ?_
    simp [map_pow]
  have hne : (((ASet m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
      ((ASet' m P ε : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 :=
    mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hη)
      (FractionalIdeal.coeIdeal_ne_zero.mpr (by rw [← conjI_ASet]; exact conjI_ne_bot hε))
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((Q : K) ^ 2 * uOf x y) ≤ 1 := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, h8, hQspan]
    calc ((Ideal.span {((Q : 𝓞 K) ^ 2)} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
            (((ASet m P ε : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
              (((ASet' m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
              ((((ASet m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
                (((ASet' m P ε : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)))⁻¹)
          = (((Ideal.span {((Q : 𝓞 K) ^ 2)} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
              (((ASet m P ε : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
              (((ASet' m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))) *
              ((((ASet m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
                (((ASet' m P ε : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)))⁻¹ := by
            ac_rfl
        _ ≤ ((((ASet m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
              (((ASet' m P ε : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))) *
              ((((ASet m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
                (((ASet' m P ε : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)))⁻¹ := by
            exact mul_le_mul_left hmain _
        _ = 1 := mul_inv_cancel₀ hne
  have hmem : (Q : K) ^ 2 * uOf x y ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.spanSingleton_le_iff_mem.mp hle
  obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hmem
  exact ⟨w, hw⟩


theorem Pigeonhole (K : Type*) [Field K] [NumberField K] [NumberField.IsCMField K]
    (m : ℕ) (P : Fin m → Ideal (𝓞 K)) (hP : ∀ i, (P i).IsPrime)
    (hPne : ∀ i j, i ≠ j → P i ≠ P j)
    (hconj : ∀ i j, Ideal.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom (P i) ≠ P j)
    (Q : ℕ) (hQ0 : 0 < Q)
    (hQ : ∀ i, ∃ p : ℕ, p ∣ Q ∧ Nat.Prime p ∧ Ideal.span {(p : 𝓞 K)} ≤ P i) :
    ∃ U : Finset K, (∀ u ∈ U, u * NumberField.IsCMField.complexConj K u = 1) ∧
      (∀ u ∈ U, ∃ w : 𝓞 K, (w : K) = (Q : K) ^ 2 * u) ∧
      U.card * NumberField.classNumber K ≥ 2 ^ m := by
  classical
  have hconj' : ∀ i j, conjI (P i) ≠ P j := fun i j => hconj i j
  have hnb : ∀ i, P i ≠ ⊥ := by
    intro i
    obtain ⟨p, -, hp, hpP⟩ := hQ i
    intro hbot
    have hmem : (p : 𝓞 K) ∈ (⊥ : Ideal (𝓞 K)) := hbot ▸ hpP (Ideal.mem_span_singleton_self _)
    have hp0 : (p : 𝓞 K) = 0 := by simpa using hmem
    exact hp.ne_zero (Nat.cast_eq_zero.mp hp0)
  let cls : (Fin m → Bool) → ClassGroup (𝓞 K) := fun ε =>
    ClassGroup.mk0 ⟨ASet m P ε, mem_nonZeroDivisors_of_ne_zero (ASet_ne_bot m P hnb ε)⟩
  obtain ⟨η, hη⟩ := PigeonholeAux.fiber cls (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩)
  let F : Finset (Fin m → Bool) := Finset.univ.filter (fun ε => cls ε = cls η)
  have hFcard : 2 ^ m ≤ F.card * NumberField.classNumber K := by
    have h2 : (2 : ℕ) ^ m = Fintype.card (Fin m → Bool) := by simp
    simpa only [h2, F, NumberField.classNumber] using hη
  have hex : ∀ ε ∈ F, ∃ x y : 𝓞 K, x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {x} * ASet m P ε = Ideal.span {y} * ASet m P η := by
    intro ε hε
    have hcls : cls ε = cls η := (Finset.mem_filter.mp hε).2
    simp only [cls] at hcls
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hcls
    exact ⟨x, y, hx, hy, hxy⟩
  choose xs ys hxs hys hspan using hex
  let uF : F → K := fun ε => uOf (xs ε.1 ε.2) (ys ε.1 ε.2)
  have hmul : ∀ ε : F, uF ε * NumberField.IsCMField.complexConj K (uF ε) = 1 := fun ε =>
    PigeonholeAux.uOf_mul_conj (xs ε.1 ε.2) (ys ε.1 ε.2) (hxs ε.1 ε.2) (hys ε.1 ε.2)
  have hint : ∀ ε : F, ∃ w : 𝓞 K, (w : K) = (Q : K) ^ 2 * uF ε := fun ε =>
    uOf_integral m P hP hPne hconj' Q hQ η ε.1 (xs ε.1 ε.2) (ys ε.1 ε.2)
      (hxs ε.1 ε.2) (hys ε.1 ε.2) (hspan ε.1 ε.2)
  have hinj : Function.Injective uF := by
    intro ε ε' h
    have h1 := PigeonholeAux.span_singleton_uOf m P η ε.1
      (ASet_ne_bot m P hnb ε.1) (ASet_ne_bot m P hnb η)
      (xs ε.1 ε.2) (ys ε.1 ε.2) (hxs ε.1 ε.2) (hys ε.1 ε.2) (hspan ε.1 ε.2)
    have h2 := PigeonholeAux.span_singleton_uOf m P η ε'.1
      (ASet_ne_bot m P hnb ε'.1) (ASet_ne_bot m P hnb η)
      (xs ε'.1 ε'.2) (ys ε'.1 ε'.2) (hxs ε'.1 ε'.2) (hys ε'.1 ε'.2) (hspan ε'.1 ε'.2)
    have hfrac :
        ((ASet m P ε.1 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
            (((ASet' m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
            ((((ASet m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
              (((ASet' m P ε.1 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)))⁻¹ =
          ((ASet m P ε'.1 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
            (((ASet' m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
            ((((ASet m P η : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
              (((ASet' m P ε'.1 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)))⁻¹ := by
      rw [← h1, ← h2]
      exact congrArg (FractionalIdeal.spanSingleton (𝓞 K)⁰) h
    exact Subtype.ext (eq_of_ASet_mul_eq m P hP hPne hconj' hnb ε.1 ε'.1
      (ASet_mul_eq_of_fractional_eq m P η ε.1 ε'.1 (ASet_ne_bot m P hnb η)
        (ASet_ne_bot m P hnb ε.1) (ASet_ne_bot m P hnb ε'.1) hfrac))
  refine ⟨F.attach.image uF, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨ε, -, rfl⟩ := Finset.mem_image.mp hu
    exact hmul ε
  · intro u hu
    obtain ⟨ε, -, rfl⟩ := Finset.mem_image.mp hu
    exact hint ε
  · have hc : (F.attach.image uF).card = F.card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
    show 2 ^ m ≤ (F.attach.image uF).card * NumberField.classNumber K
    rw [hc]
    exact hFcard

end Work.Arithmetic
