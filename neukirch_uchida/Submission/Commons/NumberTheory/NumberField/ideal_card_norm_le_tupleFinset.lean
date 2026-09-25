import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Radical.Basic
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.NumberTheory.Nat.omega_color_sum_le_harmonic
import Mathlib.Algebra.CharZero.Infinite

namespace Commons.NumberTheory.NumberField

open scoped _root_.NumberField nonZeroDivisors

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {K : Type*} [Field K] [NumberField K]

lemma primesOverFinset_card_le (p : ℕ) [Fact (Nat.Prime p)] :
    (IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (NumberField.RingOfIntegers K)).card ≤ Module.finrank ℚ K := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpZ_ne : pZ ≠ ⊥ := by
    exact (Ideal.span_singleton_eq_bot).not.mpr hp0
  have hpZ_max : pZ.IsMaximal := by
    have hpZ_prime : pZ.IsPrime := by
      exact (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))
    exact hpZ_prime.isMaximal hpZ_ne
  have h := Ideal.card_primesOverFinset_le_finrank (R := ℤ) (S := NumberField.RingOfIntegers K) (K := ℚ) (L := K)
    (p := pZ) hpZ_ne
  simpa [NumberField.RingOfIntegers.rank K] using h

noncomputable def primesOverIndex (p : ℕ) [Fact (Nat.Prime p)] :
    {P : Ideal (NumberField.RingOfIntegers K) // P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (NumberField.RingOfIntegers K)} ↪ Fin (Module.finrank ℚ K) := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let s : Finset (Ideal (NumberField.RingOfIntegers K)) := IsDedekindDomain.primesOverFinset pZ (NumberField.RingOfIntegers K)
  have hcard : Fintype.card {P : Ideal (NumberField.RingOfIntegers K) // P ∈ s} ≤ Fintype.card (Fin (Module.finrank ℚ K)) := by
    simpa using primesOverFinset_card_le (K := K) p
  exact Classical.choice (Function.Embedding.nonempty_of_card_le (α := {P : Ideal (NumberField.RingOfIntegers K) // P ∈ s}) (β := Fin (Module.finrank ℚ K)) hcard)

noncomputable def primeIndex (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    Fin (Module.finrank ℚ K) := by
  classical
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  haveI : P.IsPrime := hP
  haveI : NeZero P := ⟨hP0⟩
  have hp : Nat.Prime p := by
    dsimp [p]
    exact Nat.absNorm_under_prime P
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hpZ_ne : pZ ≠ ⊥ := by
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact (Ideal.span_singleton_eq_bot).not.mpr hp0
  have hpZ_max : pZ.IsMaximal := by
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpZ_prime : pZ.IsPrime := by
      exact (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)
    exact hpZ_prime.isMaximal hpZ_ne
  let s : Finset (Ideal (NumberField.RingOfIntegers K)) := IsDedekindDomain.primesOverFinset pZ (NumberField.RingOfIntegers K)
  have hmem : P ∈ s := by
    have hpr : P ∈ pZ.primesOver (NumberField.RingOfIntegers K) := ⟨hP, by
      simpa [p, pZ] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))⟩
    exact (IsDedekindDomain.mem_primesOverFinset_iff hpZ_ne (B := NumberField.RingOfIntegers K)).mpr hpr
  exact (primesOverIndex (K := K) p) ⟨P, hmem⟩

lemma primeIndex_underlying_liesOver (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)) := by
  simpa using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))

lemma primeIndex_underlying_prime (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    Nat.Prime (Ideal.absNorm (Ideal.under ℤ P)) := by
  haveI : P.IsPrime := hP
  haveI : NeZero P := ⟨hP0⟩
  exact Nat.absNorm_under_prime P

noncomputable def idealToTuple (I : (Ideal (NumberField.RingOfIntegers K))⁰) : Fin (Module.finrank ℚ K) → ℕ := by
  classical
  let J : Ideal (NumberField.RingOfIntegers K) := I
  have hJ : J ≠ ⊥ := by
    dsimp [J]
    simpa using (nonZeroDivisors.coe_ne_zero I)
  let fac : Multiset (Ideal (NumberField.RingOfIntegers K)) := UniqueFactorizationMonoid.normalizedFactors J
  exact fun i => ∏ P : {P : Ideal (NumberField.RingOfIntegers K) // P ∈ fac.toFinset},
    let Q : Ideal (NumberField.RingOfIntegers K) := P.1
    let hPs : Q ∈ fac.toFinset := P.2
    let hPfac : Q ∈ fac := Multiset.mem_toFinset.mp hPs
    let hPprime : Q.IsPrime := ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).1
    let hP0 : Q ≠ ⊥ := by
      intro hPbot
      have hJle : J ≤ ⊥ := by
        simpa [hPbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).2
      exact hJ (le_bot_iff.mp hJle)
    if primeIndex (K := K) Q hPprime hP0 = i then Ideal.absNorm Q ^ fac.count Q else 1

lemma idealToTuple_prod (I : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∏ i : Fin (Module.finrank ℚ K), idealToTuple I i = Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) := by
  classical
  let J : Ideal (NumberField.RingOfIntegers K) := I
  have hJ : J ≠ ⊥ := by
    dsimp [J]
    simpa using (nonZeroDivisors.coe_ne_zero I)
  let fac : Multiset (Ideal (NumberField.RingOfIntegers K)) := UniqueFactorizationMonoid.normalizedFactors J
  have hfac_prod : fac.prod = J := by
    dsimp [fac]
    exact Ideal.prod_normalizedFactors_eq_self hJ
  have habs : Ideal.absNorm J = (fac.map (fun P => Ideal.absNorm P)).prod := by
    rw [← hfac_prod]
    exact map_multiset_prod (Ideal.absNorm) fac
  calc
    ∏ i : Fin (Module.finrank ℚ K), idealToTuple I i
        = ∏ i : Fin (Module.finrank ℚ K), ∏ P : {P : Ideal (NumberField.RingOfIntegers K) // P ∈ fac.toFinset},
            (if primeIndex (K := K) P.1 (by
                have hPfac : P.1 ∈ fac := Multiset.mem_toFinset.mp P.2
                exact ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).1)
              (by
                have hPfac : P.1 ∈ fac := Multiset.mem_toFinset.mp P.2
                intro hPbot
                have hJle : J ≤ ⊥ := by
                  simpa [hPbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).2
                exact hJ (le_bot_iff.mp hJle)) = i then
              Ideal.absNorm P.1 ^ fac.count P.1 else 1) := by
          simp [idealToTuple, J, fac]
    _ = ∏ P : {P : Ideal (NumberField.RingOfIntegers K) // P ∈ fac.toFinset},
          ∏ i : Fin (Module.finrank ℚ K),
            (if primeIndex (K := K) P.1 (by
                have hPfac : P.1 ∈ fac := Multiset.mem_toFinset.mp P.2
                exact ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).1)
              (by
                have hPfac : P.1 ∈ fac := Multiset.mem_toFinset.mp P.2
                intro hPbot
                have hJle : J ≤ ⊥ := by
                  simpa [hPbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).2
                exact hJ (le_bot_iff.mp hJle)) = i then
              Ideal.absNorm P.1 ^ fac.count P.1 else 1) := by
          rw [Finset.prod_comm]
    _ = ∏ P : {P : Ideal (NumberField.RingOfIntegers K) // P ∈ fac.toFinset},
          Ideal.absNorm P.1 ^ fac.count P.1 := by
          apply Finset.prod_congr rfl
          intro P hP
          let Q : Ideal (NumberField.RingOfIntegers K) := P.1
          have hPfac : Q ∈ fac := Multiset.mem_toFinset.mp P.2
          have hPprime : Q.IsPrime := ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).1
          have hP0 : Q ≠ ⊥ := by
            intro hPbot
            have hJle : J ≤ ⊥ := by
              simpa [hPbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).2
            exact hJ (le_bot_iff.mp hJle)
          change (∏ i : Fin (Module.finrank ℚ K),
              (if primeIndex (K := K) Q hPprime hP0 = i then Ideal.absNorm Q ^ fac.count Q else 1))
              = Ideal.absNorm Q ^ fac.count Q
          rw [Finset.prod_ite_eq]
          simp
    _ = ∏ P ∈ fac.toFinset, Ideal.absNorm P ^ fac.count P := by
          exact (Finset.prod_coe_sort fac.toFinset (fun P => Ideal.absNorm P ^ fac.count P))
    _ = (fac.map (fun P => Ideal.absNorm P)).prod := by
          rw [Finset.prod_multiset_map_count]
    _ = Ideal.absNorm J := habs.symm
    _ = Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) := by simp [J]

lemma idealToTuple_one_le (I : (Ideal (NumberField.RingOfIntegers K))⁰) (i : Fin (Module.finrank ℚ K)) :
    1 ≤ idealToTuple I i := by
  classical
  let J : Ideal (NumberField.RingOfIntegers K) := I
  have hJ : J ≠ ⊥ := by
    dsimp [J]
    simpa using (nonZeroDivisors.coe_ne_zero I)
  let fac : Multiset (Ideal (NumberField.RingOfIntegers K)) := UniqueFactorizationMonoid.normalizedFactors J
  dsimp [idealToTuple]
  apply Finset.one_le_prod₀
  intro P hP
  let Q : Ideal (NumberField.RingOfIntegers K) := P.1
  have hPs : Q ∈ fac.toFinset := P.2
  have hPfac : Q ∈ fac := Multiset.mem_toFinset.mp hPs
  have hPprime : Q.IsPrime := ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).1
  have hP0 : Q ≠ ⊥ := by
    intro hPbot
    have hJle : J ≤ ⊥ := by
      simpa [hPbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).2
    exact hJ (le_bot_iff.mp hJle)
  change 1 ≤ if primeIndex (K := K) Q hPprime hP0 = i then Ideal.absNorm Q ^ fac.count Q else 1
  by_cases h : primeIndex (K := K) Q hPprime hP0 = i
  · simp [h]
    apply one_le_pow₀
    exact Nat.succ_le_iff.mpr (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero hP0))
  · simp [h]

lemma idealToTuple_mem_tupleFinset (A : ℕ)
    (I : {I : (Ideal (NumberField.RingOfIntegers K))⁰ // Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ A}) :
    idealToTuple I.1 ∈ Commons.NumberTheory.Nat.tupleFinset (Module.finrank ℚ K) A := by
  classical
  rw [Commons.NumberTheory.Nat.mem_tupleFinset]
  constructor
  · intro i
    have h1 : 1 ≤ idealToTuple I.1 i := idealToTuple_one_le I.1 i
    have hle : idealToTuple I.1 i ≤ ∏ j : Fin (Module.finrank ℚ K), idealToTuple I.1 j := by
      have hsingle := Finset.single_le_prod' (s := (Finset.univ : Finset (Fin (Module.finrank ℚ K))))
        (f := idealToTuple I.1) (fun j hj => idealToTuple_one_le I.1 j) (a := i) (Finset.mem_univ i)
      simpa using hsingle
    have hprod : (∏ j : Fin (Module.finrank ℚ K), idealToTuple I.1 j) ≤ A := by
      rw [idealToTuple_prod I.1]
      exact I.2
    exact Finset.mem_Icc.mpr ⟨h1, le_trans hle hprod⟩
  · rw [idealToTuple_prod I.1]
    exact I.2

lemma underlying_absNorm_eq_of_liesOver {P : Ideal (NumberField.RingOfIntegers K)} {p : ℕ}
    (hp : Nat.Prime p) (hPl : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    Ideal.absNorm (Ideal.under ℤ P) = p := by
  classical
  let m : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  have hlie_m : P.LiesOver (Ideal.span ({(m : ℤ)} : Set ℤ)) := by
    simpa [m] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))
  have hm_under : Ideal.span ({(m : ℤ)} : Set ℤ) = Ideal.under ℤ P := by
    exact (Ideal.liesOver_iff P (Ideal.span ({(m : ℤ)} : Set ℤ))).mp hlie_m
  have hp_under : Ideal.span ({(p : ℤ)} : Set ℤ) = Ideal.under ℤ P := by
    exact (Ideal.liesOver_iff P (Ideal.span ({(p : ℤ)} : Set ℤ))).mp hPl
  have hsp : Ideal.span ({(m : ℤ)} : Set ℤ) = Ideal.span ({(p : ℤ)} : Set ℤ) := by
    rw [hm_under, hp_under]
  have hle_mp : Ideal.span ({(m : ℤ)} : Set ℤ) ≤ Ideal.span ({(p : ℤ)} : Set ℤ) := le_of_eq hsp
  have hle_pm : Ideal.span ({(p : ℤ)} : Set ℤ) ≤ Ideal.span ({(m : ℤ)} : Set ℤ) := le_of_eq hsp.symm
  have hdiv_pm : (p : ℤ) ∣ (m : ℤ) := by
    exact (Ideal.span_singleton_le_span_singleton.mp hle_mp)
  have hdiv_mp : (m : ℤ) ∣ (p : ℤ) := by
    exact (Ideal.span_singleton_le_span_singleton.mp hle_pm)
  have hdiv_pm_nat : p ∣ m := Int.natCast_dvd_natCast.mp hdiv_pm
  have hdiv_mp_nat : m ∣ p := Int.natCast_dvd_natCast.mp hdiv_mp
  exact Nat.dvd_antisymm hdiv_mp_nat hdiv_pm_nat

lemma primeIndex_inj_of_liesOver {P Q : Ideal (NumberField.RingOfIntegers K)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥)
    {p : ℕ} (hp : Nat.Prime p)
    (hPl : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    (hQl : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    (h : primeIndex (K := K) P hP hP0 = primeIndex (K := K) Q hQ hQ0) :
    P = Q := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpZ_ne : pZ ≠ ⊥ := by
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact (Ideal.span_singleton_eq_bot).not.mpr hp0
  have hmemP : P ∈ IsDedekindDomain.primesOverFinset pZ (NumberField.RingOfIntegers K) := by
    have hpr : P ∈ pZ.primesOver (NumberField.RingOfIntegers K) := ⟨hP, hPl⟩
    exact (IsDedekindDomain.mem_primesOverFinset_iff hpZ_ne (B := NumberField.RingOfIntegers K)).mpr hpr
  have hmemQ : Q ∈ IsDedekindDomain.primesOverFinset pZ (NumberField.RingOfIntegers K) := by
    have hpr : Q ∈ pZ.primesOver (NumberField.RingOfIntegers K) := ⟨hQ, hQl⟩
    exact (IsDedekindDomain.mem_primesOverFinset_iff hpZ_ne (B := NumberField.RingOfIntegers K)).mpr hpr
  have hPidx : primeIndex (K := K) P hP hP0 = (primesOverIndex (K := K) p) ⟨P, hmemP⟩ := by
    have hmp : Ideal.absNorm (Ideal.under ℤ P) = p := underlying_absNorm_eq_of_liesOver hp hPl
    subst p
    unfold primeIndex
    rfl
  have hQidx : primeIndex (K := K) Q hQ hQ0 = (primesOverIndex (K := K) p) ⟨Q, hmemQ⟩ := by
    have hmq : Ideal.absNorm (Ideal.under ℤ Q) = p := underlying_absNorm_eq_of_liesOver hp hQl
    subst p
    unfold primeIndex
    rfl
  have hemb : (primesOverIndex (K := K) p) ⟨P, hmemP⟩ = (primesOverIndex (K := K) p) ⟨Q, hmemQ⟩ := by
    rw [← hPidx, ← hQidx]
    exact h
  have hsub := (primesOverIndex (K := K) p).injective hemb
  simpa using congrArg Subtype.val hsub

lemma absNorm_pow_factorization_eq (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (c : ℕ) :
    (Ideal.absNorm P ^ c).factorization (Ideal.absNorm (Ideal.under ℤ P)) =
      (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)).inertiaDeg' P * c := by
  classical
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp : Nat.Prime p := by
    dsimp [p]
    haveI : P.IsPrime := hP
    haveI : NeZero P := ⟨hP0⟩
    exact Nat.absNorm_under_prime P
  have hPl : P.LiesOver pZ := by
    simpa [p, pZ] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))
  have hnorm : Ideal.absNorm P = p ^ (pZ.inertiaDeg' P) := by
    exact Ideal.absNorm_eq_pow_inertiaDeg' (R := NumberField.RingOfIntegers K) P hp
  have hpow : (Ideal.absNorm P ^ c).factorization p = (p ^ (pZ.inertiaDeg' P * c)).factorization p := by
    rw [hnorm, pow_mul]
  rw [hpow, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]

lemma absNorm_pow_factorization_eq_zero_of_not_liesOver {Q : Ideal (NumberField.RingOfIntegers K)}
    (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) {p : ℕ} (hp : Nat.Prime p)
    (hnot : ¬ Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) (c : ℕ) :
    (Ideal.absNorm Q ^ c).factorization p = 0 := by
  classical
  let q : ℕ := Ideal.absNorm (Ideal.under ℤ Q)
  have hq : Nat.Prime q := by
    dsimp [q]
    haveI : Q.IsPrime := hQ
    haveI : NeZero Q := ⟨hQ0⟩
    exact Nat.absNorm_under_prime Q
  let qZ : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
  have hQl : Q.LiesOver qZ := by
    simpa [q, qZ] using (inferInstance : Q.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ Q) : ℤ)} : Set ℤ)))
  have hnorm : Ideal.absNorm Q = q ^ (qZ.inertiaDeg' Q) := by
    exact Ideal.absNorm_eq_pow_inertiaDeg' (R := NumberField.RingOfIntegers K) Q hq
  have hnot_dvd : ¬ p ∣ Ideal.absNorm Q := by
    intro hpdvd
    have hpdvd_pow : p ∣ q ^ (qZ.inertiaDeg' Q) := by
      simpa [hnorm] using hpdvd
    have hqp : q = p := by
      have hp_dvd_q : p ∣ q := Nat.Prime.dvd_of_dvd_pow hp hpdvd_pow
      exact (hq.dvd_iff_eq hp.ne_one).mp hp_dvd_q
    have hQp : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
      simpa [qZ, hqp] using hQl
    exact hnot hQp
  rw [Nat.factorization_pow]
  have hfac_zero : (Ideal.absNorm Q).factorization p = 0 := by
    exact Nat.factorization_eq_zero_of_not_dvd hnot_dvd
  simp [hfac_zero]

lemma factorization_idealToTuple_entry (I : (Ideal (NumberField.RingOfIntegers K))⁰) {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hPfac : P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) :
    (idealToTuple I (primeIndex (K := K) P hP hP0)).factorization (Ideal.absNorm (Ideal.under ℤ P)) =
      (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)).inertiaDeg' P *
        (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))).count P := by
  classical
  let J : Ideal (NumberField.RingOfIntegers K) := I
  have hJ : J ≠ ⊥ := by
    dsimp [J]
    simpa using (nonZeroDivisors.coe_ne_zero I)
  let fac : Multiset (Ideal (NumberField.RingOfIntegers K)) := UniqueFactorizationMonoid.normalizedFactors J
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let idx : Fin (Module.finrank ℚ K) := primeIndex (K := K) P hP hP0
  have hp : Nat.Prime p := by
    dsimp [p]
    haveI : P.IsPrime := hP
    haveI : NeZero P := ⟨hP0⟩
    exact Nat.absNorm_under_prime P
  have hPl : P.LiesOver pZ := by
    simpa [p, pZ] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))
  have hPmem : P ∈ fac.toFinset := by
    dsimp [fac, J]
    exact Multiset.mem_toFinset.mpr hPfac
  let T := {Q : Ideal (NumberField.RingOfIntegers K) // Q ∈ fac.toFinset}
  have hQfac_of : ∀ Q : T, Q.1 ∈ fac := fun Q => Multiset.mem_toFinset.mp Q.2
  have hQprime_of : ∀ Q : T, Q.1.IsPrime := fun Q =>
    ((Ideal.mem_normalizedFactors_iff hJ).mp (hQfac_of Q)).1
  have hQ0_of : ∀ Q : T, Q.1 ≠ ⊥ := by
    intro Q hbot
    have hJle : J ≤ ⊥ := by
      simpa [hbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp (hQfac_of Q)).2
    exact hJ (le_bot_iff.mp hJle)
  let g : T → ℕ := fun Q =>
    if primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx then
      Ideal.absNorm Q.1 ^ fac.count Q.1 else 1
  have hg_ne : ∀ Q ∈ (Finset.univ : Finset T), g Q ≠ 0 := by
    intro Q hQ
    dsimp [g]
    by_cases h : primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx
    · rw [if_pos h]
      exact pow_ne_zero _ (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero (hQ0_of Q)))
    · rw [if_neg h]
      exact one_ne_zero
  have hprod_fac : (∏ Q : T, g Q).factorization = ∑ Q : T, (g Q).factorization := by
    exact Nat.factorization_prod (S := (Finset.univ : Finset T)) (g := g) hg_ne
  have hprod_eval : (∏ Q : T, g Q).factorization p = ∑ Q : T, (g Q).factorization p := by
    rw [hprod_fac, Finsupp.finset_sum_apply]
  have hterm_P : (g (⟨P, hPmem⟩ : T)).factorization p = pZ.inertiaDeg' P * fac.count P := by
    dsimp [g]
    have hpr : primeIndex (K := K) P hP hP0 = idx := rfl
    rw [if_pos hpr]
    simpa [p, pZ] using absNorm_pow_factorization_eq P hP hP0 (fac.count P)
  have hterm_other : ∀ Q : T, Q ≠ (⟨P, hPmem⟩ : T) → (g Q).factorization p = 0 := by
    intro Q hQne
    dsimp [g]
    by_cases h : primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx
    · rw [if_pos h]
      have hnot_lie : ¬ Q.1.LiesOver pZ := by
        intro hlie
        have h_eq := primeIndex_inj_of_liesOver (K := K) hP hP0 (hQprime_of Q) (hQ0_of Q) hp hPl hlie
            (by simpa [idx] using h.symm)
        have hsub : Q = (⟨P, hPmem⟩ : T) := Subtype.ext h_eq.symm
        exact hQne hsub
      exact absNorm_pow_factorization_eq_zero_of_not_liesOver (hQprime_of Q) (hQ0_of Q) hp hnot_lie (fac.count Q.1)
    · rw [if_neg h]
      simp
  have hsum_eq : (∑ Q : T, (g Q).factorization p) = pZ.inertiaDeg' P * fac.count P := by
    rw [Finset.sum_eq_single (⟨P, hPmem⟩ : T)]
    · exact hterm_P
    · intro b hb hne
      exact hterm_other b hne
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  have hmain : (idealToTuple I idx).factorization p = pZ.inertiaDeg' P * fac.count P := by
    dsimp [idealToTuple, J, fac]
    change (∏ Q : T, g Q).factorization p = pZ.inertiaDeg' P * fac.count P
    rw [hprod_eval, hsum_eq]
  simpa [p, pZ, idx, fac, J] using hmain

lemma factorization_idealToTuple_entry_eq_zero_of_not_mem (J : (Ideal (NumberField.RingOfIntegers K))⁰) {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hPnot : P ∉ (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))).toFinset) :
    (idealToTuple J (primeIndex (K := K) P hP hP0)).factorization (Ideal.absNorm (Ideal.under ℤ P)) = 0 := by
  classical
  let I0 : Ideal (NumberField.RingOfIntegers K) := J
  have hI0 : I0 ≠ ⊥ := by
    dsimp [I0]
    simpa using (nonZeroDivisors.coe_ne_zero J)
  let fac : Multiset (Ideal (NumberField.RingOfIntegers K)) := UniqueFactorizationMonoid.normalizedFactors I0
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let idx : Fin (Module.finrank ℚ K) := primeIndex (K := K) P hP hP0
  have hp : Nat.Prime p := by
    dsimp [p]
    haveI : P.IsPrime := hP
    haveI : NeZero P := ⟨hP0⟩
    exact Nat.absNorm_under_prime P
  have hPl : P.LiesOver pZ := by
    simpa [p, pZ] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))
  have hPnot_fac : P ∉ fac.toFinset := by
    simpa [fac, I0] using hPnot
  let T := {Q : Ideal (NumberField.RingOfIntegers K) // Q ∈ fac.toFinset}
  have hQfac_of : ∀ Q : T, Q.1 ∈ fac := fun Q => Multiset.mem_toFinset.mp Q.2
  have hQprime_of : ∀ Q : T, Q.1.IsPrime := fun Q =>
    ((Ideal.mem_normalizedFactors_iff hI0).mp (hQfac_of Q)).1
  have hQ0_of : ∀ Q : T, Q.1 ≠ ⊥ := by
    intro Q hbot
    have hI0le : I0 ≤ ⊥ := by
      simpa [hbot] using ((Ideal.mem_normalizedFactors_iff hI0).mp (hQfac_of Q)).2
    exact hI0 (le_bot_iff.mp hI0le)
  let g : T → ℕ := fun Q =>
    if primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx then
      Ideal.absNorm Q.1 ^ fac.count Q.1 else 1
  have hg_ne : ∀ Q ∈ (Finset.univ : Finset T), g Q ≠ 0 := by
    intro Q hQ
    dsimp [g]
    by_cases h : primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx
    · rw [if_pos h]
      exact pow_ne_zero _ (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero (hQ0_of Q)))
    · rw [if_neg h]
      exact one_ne_zero
  have hprod_fac : (∏ Q : T, g Q).factorization = ∑ Q : T, (g Q).factorization := by
    exact Nat.factorization_prod (S := (Finset.univ : Finset T)) (g := g) hg_ne
  have hprod_eval : (∏ Q : T, g Q).factorization p = ∑ Q : T, (g Q).factorization p := by
    rw [hprod_fac, Finsupp.finset_sum_apply]
  have hterm_other : ∀ Q : T, (g Q).factorization p = 0 := by
    intro Q
    dsimp [g]
    by_cases h : primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx
    · rw [if_pos h]
      have hnot_lie : ¬ Q.1.LiesOver pZ := by
        intro hlie
        have h_eq := primeIndex_inj_of_liesOver (K := K) hP hP0 (hQprime_of Q) (hQ0_of Q) hp hPl hlie
            (by simpa [idx] using h.symm)
        have hPQ : P = Q.1 := h_eq
        have hPmem : P ∈ fac.toFinset := by
          rw [hPQ]
          exact Q.2
        exact hPnot_fac hPmem
      exact absNorm_pow_factorization_eq_zero_of_not_liesOver (hQprime_of Q) (hQ0_of Q) hp hnot_lie (fac.count Q.1)
    · rw [if_neg h]
      simp
  have hsum_zero : (∑ Q : T, (g Q).factorization p) = 0 := by
    exact Finset.sum_eq_zero (fun Q hQ => hterm_other Q)
  have hmain : (idealToTuple J idx).factorization p = 0 := by
    dsimp [idealToTuple, I0, fac]
    change (∏ Q : T, g Q).factorization p = 0
    rw [hprod_eval, hsum_zero]
  simpa [p, idx, fac, I0] using hmain

lemma idealToTuple_injective :
    Function.Injective (fun I : (Ideal (NumberField.RingOfIntegers K))⁰ => idealToTuple I) := by
  classical
  intro I J h
  apply Subtype.ext
  have hI_ne : (I : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    simpa using (nonZeroDivisors.coe_ne_zero I)
  have hJ_ne : (J : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    simpa using (nonZeroDivisors.coe_ne_zero J)
  have hfac_eq : UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K)) =
      UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K)) := by
    rw [Multiset.ext]
    intro P
    by_cases hPprime : P.IsPrime
    · by_cases hP0 : P ≠ ⊥
      · let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
        let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
        let idx : Fin (Module.finrank ℚ K) := primeIndex (K := K) P hPprime hP0
        have hp : Nat.Prime p := by
          dsimp [p]
          haveI : P.IsPrime := hPprime
          haveI : NeZero P := ⟨hP0⟩
          exact Nat.absNorm_under_prime P
        have hPl : P.LiesOver pZ := by
          simpa [p, pZ] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))
        have hf_pos : 0 < pZ.inertiaDeg' P := by
          haveI : P.IsPrime := hPprime
          haveI : P.LiesOver pZ := hPl
          exact Ideal.inertiaDeg'_pos' pZ P
        have h_entry : idealToTuple I idx = idealToTuple J idx := by
          exact congrFun h idx
        have hval_eq : (idealToTuple I idx).factorization p = (idealToTuple J idx).factorization p := by
          rw [h_entry]
        -- show counts equal by cases on membership
        by_cases hPfacI : P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))
        · have hPmemI : P ∈ (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))).toFinset :=
            Multiset.mem_toFinset.mpr hPfacI
          have hvalI := factorization_idealToTuple_entry I hPprime hP0 hPfacI
          have hcountI_pos : 0 < Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) :=
            Multiset.count_pos.mpr hPfacI
          have hPfacJ : P ∈ UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K)) := by
            by_contra hnot
            have hPnotJ : P ∉ (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))).toFinset :=
              Multiset.mem_toFinset.not.mpr hnot
            have hvalJ0 := factorization_idealToTuple_entry_eq_zero_of_not_mem J hPprime hP0 hPnotJ
            have hvalI' : (idealToTuple I idx).factorization p = pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) := by
              simpa [p, pZ, idx] using hvalI
            have hvalJ' : (idealToTuple J idx).factorization p = 0 := by
              simpa [p, pZ, idx] using hvalJ0
            have hnonzero : pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) ≠ 0 := by
              exact Nat.mul_ne_zero (Nat.ne_of_gt hf_pos) (Nat.ne_of_gt hcountI_pos)
            exact hnonzero (by rw [← hvalI', hval_eq, hvalJ'])
          have hvalJ := factorization_idealToTuple_entry J hPprime hP0 hPfacJ
          have hvalI' : (idealToTuple I idx).factorization p = pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) := by
            simpa [p, pZ, idx] using hvalI
          have hvalJ' : (idealToTuple J idx).factorization p = pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))) := by
            simpa [p, pZ, idx] using hvalJ
          have hmul : pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) =
              pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))) := by
            rw [← hvalI', hval_eq, hvalJ']
          exact Nat.mul_left_cancel hf_pos hmul
        · have hPfacI_not : P ∉ (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))).toFinset :=
            Multiset.mem_toFinset.not.mpr hPfacI
          have hvalI0 := factorization_idealToTuple_entry_eq_zero_of_not_mem I hPprime hP0 hPfacI_not
          by_cases hPfacJ : P ∈ UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))
          · have hPmemJ : P ∈ (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))).toFinset :=
              Multiset.mem_toFinset.mpr hPfacJ
            have hvalJ := factorization_idealToTuple_entry J hPprime hP0 hPfacJ
            have hcountJ_pos : 0 < Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))) :=
              Multiset.count_pos.mpr hPfacJ
            have hvalI' : (idealToTuple I idx).factorization p = 0 := by
              simpa [p, pZ, idx] using hvalI0
            have hvalJ' : (idealToTuple J idx).factorization p = pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))) := by
              simpa [p, pZ, idx] using hvalJ
            have hnonzero : pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))) ≠ 0 := by
              exact Nat.mul_ne_zero (Nat.ne_of_gt hf_pos) (Nat.ne_of_gt hcountJ_pos)
            exfalso
            exact hnonzero (by rw [← hvalJ', ← hval_eq, hvalI'])
          · rw [Multiset.count_eq_zero.mpr hPfacI, Multiset.count_eq_zero.mpr hPfacJ]
      · -- P = ⊥, count zero for both
        have hPbot : P = ⊥ := by simpa using hP0
        subst P
        have hI_bot_not : (⊥ : Ideal (NumberField.RingOfIntegers K)) ∉ UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K)) := by
          intro hmem
          exact hI_ne (le_bot_iff.mp ((Ideal.mem_normalizedFactors_iff hI_ne).mp hmem).2)
        have hJ_bot_not : (⊥ : Ideal (NumberField.RingOfIntegers K)) ∉ UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K)) := by
          intro hmem
          exact hJ_ne (le_bot_iff.mp ((Ideal.mem_normalizedFactors_iff hJ_ne).mp hmem).2)
        rw [Multiset.count_eq_zero.mpr hI_bot_not, Multiset.count_eq_zero.mpr hJ_bot_not]
    · -- P not prime, count zero for both
      have hI_not : P ∉ UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K)) := by
        intro hmem
        exact hPprime ((Ideal.mem_normalizedFactors_iff hI_ne).mp hmem).1
      have hJ_not : P ∉ UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K)) := by
        intro hmem
        exact hPprime ((Ideal.mem_normalizedFactors_iff hJ_ne).mp hmem).1
      rw [Multiset.count_eq_zero.mpr hI_not, Multiset.count_eq_zero.mpr hJ_not]
  have hI_eq : (I : Ideal (NumberField.RingOfIntegers K)) = (J : Ideal (NumberField.RingOfIntegers K)) := by
    calc
      (I : Ideal (NumberField.RingOfIntegers K)) = (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))).prod :=
        (Ideal.prod_normalizedFactors_eq_self hI_ne).symm
      _ = (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))).prod := by rw [hfac_eq]
      _ = (J : Ideal (NumberField.RingOfIntegers K)) := Ideal.prod_normalizedFactors_eq_self hJ_ne
  exact hI_eq

theorem ideal_card_norm_le_tupleFinset (K : Type*) [Field K] [NumberField K] (A : ℕ) :
    Nat.card {I : (Ideal (NumberField.RingOfIntegers K))⁰ //
      Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ A} ≤
      (Commons.NumberTheory.Nat.tupleFinset (Module.finrank ℚ K) A).card := by
  classical
  let S := {I : (Ideal (NumberField.RingOfIntegers K))⁰ // Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ A}
  let f : S → Fin (Module.finrank ℚ K) → ℕ := fun I => idealToTuple I.1
  have hf_inj : Function.Injective f := by
    intro I J h
    apply Subtype.ext
    exact idealToTuple_injective h
  have hfinS : {I : (Ideal (NumberField.RingOfIntegers K))⁰ | Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ A}.Finite := by
    exact Ideal.finite_setOfPred_absNorm_le₀ A
  haveI : Fintype S := by
    dsimp [S]
    exact hfinS.fintype
  have hcard_image : (Finset.univ.image f).card = Fintype.card S := by
    rw [Finset.card_image_of_injective (s := (Finset.univ : Finset S)) hf_inj]
    simp
  have hsub : Finset.univ.image f ⊆ Commons.NumberTheory.Nat.tupleFinset (Module.finrank ℚ K) A := by
    rw [Finset.image_subset_iff]
    intro I hI
    exact idealToTuple_mem_tupleFinset A I
  have hle_fintype : Fintype.card S ≤ (Commons.NumberTheory.Nat.tupleFinset (Module.finrank ℚ K) A).card := by
    rw [← hcard_image]
    exact Finset.card_le_card hsub
  simpa [S] using hle_fintype


end Commons.NumberTheory.NumberField