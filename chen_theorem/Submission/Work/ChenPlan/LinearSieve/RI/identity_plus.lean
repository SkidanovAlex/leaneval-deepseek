import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.identity_defs
import Submission.Work.ChenPlan.LinearSieve.RI.Gp_Gm_split
import Submission.Work.ChenPlan.LinearSieve.RI.T_ne_zero_le
import Submission.Work.ChenPlan.LinearSieve.RI.T_eq_zero_of_le
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_error_le

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ChenPlan.LinearSieve.RI

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

/-! ## The set of primes of `P` below `z` -/

def primesLt (A : BoundingSieve) (z : ℝ) : Finset ℕ :=
  A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)

lemma Pz_eq_prod (A : BoundingSieve) (z : ℝ) : Pz A z = ∏ p ∈ primesLt A z, p := rfl

lemma VfR_eq_prod (A : BoundingSieve) (z : ℝ) :
    VfR A z = ∏ p ∈ primesLt A z, (1 - A.nu p) := rfl

lemma primesLt_insert (A : BoundingSieve) {z : ℝ} {q : ℕ}
    (hq : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    primesLt A z = insert q (primesLt A q) := by
  ext p
  simp only [primesLt, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hp, hpz⟩
    rcases eq_or_ne p q with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨hp, by exact_mod_cast (lt_of_le_of_ne (hmax p hp hpz) hne)⟩
  · rintro (rfl | ⟨hp, hpq⟩)
    · exact ⟨hq, hqz⟩
    · exact ⟨hp, lt_trans (by exact_mod_cast hpq) hqz⟩

lemma not_mem_primesLt_self (A : BoundingSieve) (q : ℕ) : q ∉ primesLt A q :=
  fun hmem => lt_irrefl _ (Finset.mem_filter.mp hmem).2

lemma Pz_split (A : BoundingSieve) {z : ℝ} {q : ℕ}
    (hq : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    Pz A z = q * Pz A q := by
  rw [Pz_eq_prod A z, Pz_eq_prod A q, primesLt_insert A hq hqz hmax,
    Finset.prod_insert (not_mem_primesLt_self A q)]

lemma VfR_split' (A : BoundingSieve) {z : ℝ} {q : ℕ}
    (hq : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    VfR A z = (1 - A.nu q) * VfR A q := by
  rw [VfR_eq_prod A z, VfR_eq_prod A q, primesLt_insert A hq hqz hmax,
    Finset.prod_insert (not_mem_primesLt_self A q)]

/-! ## `Tcond` -/

lemma Tcond_one_iff (D : ℝ) (q : ℕ) : Tcond 1 D q ↔ D < (q : ℝ) ^ 3 := by
  unfold Tcond; simp

lemma Tcond_odd_ge_three (D : ℝ) (q : ℕ) {n : ℕ} (h2 : 2 ≤ n) (hodd : Odd n) :
    Tcond n D q ↔ (q : ℝ) ^ 3 ≤ D := by
  unfold Tcond
  constructor
  · intro h; exact h.2 h2 hodd
  · intro h; exact ⟨fun hn1 => absurd hn1 (by omega), fun _ _ => h⟩

lemma Tcond_even (D : ℝ) (q : ℕ) {n : ℕ} (h2 : 2 ≤ n) (heven : Even n) : Tcond n D q :=
  ⟨fun hn1 => absurd hn1 (by omega), fun _ hodd => absurd hodd (Nat.not_odd_iff_even.mpr heven)⟩

/-! ## Splitting `T` at the top prime -/

lemma T_split_succ (A : BoundingSieve) {z D : ℝ} {q m : ℕ}
    (hq : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    T A (m + 1) D z
      = T A (m + 1) D q + (if Tcond (m + 1) D q then A.nu q * T A m (D / q) q else 0) := by
  rw [T.eq_2 A D z m, T.eq_2 A D q m]
  have hset : primesLt A z = insert q (primesLt A q) := primesLt_insert A hq hqz hmax
  have hqnot : q ∉ primesLt A q := not_mem_primesLt_self A q
  rw [show A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z ∧ Tcond (m + 1) D p)
      = (primesLt A z).filter (fun p : ℕ => Tcond (m + 1) D p) from by
        rw [primesLt, Finset.filter_filter]]
  rw [show A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < q ∧ Tcond (m + 1) D p)
      = (primesLt A q).filter (fun p : ℕ => Tcond (m + 1) D p) from by
        rw [primesLt, Finset.filter_filter]]
  rw [hset, Finset.filter_insert]
  have hqX : q ∉ (primesLt A q).filter (fun p : ℕ => Tcond (m + 1) D p) :=
    fun hmem => hqnot (Finset.mem_filter.mp hmem).1
  by_cases hc : Tcond (m + 1) D q
  · rw [if_pos hc, if_pos hc, Finset.sum_insert hqX]
    ring
  · rw [if_neg hc, if_neg hc]
    ring

lemma T_split (A : BoundingSieve) {z D : ℝ} {q m : ℕ} (hm : 1 ≤ m)
    (hq : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    T A m D z = T A m D q + (if Tcond m D q then A.nu q * T A (m - 1) (D / q) q else 0) := by
  have h := T_split_succ A (z := z) (D := D) (q := q) (m := m - 1) hq hqz hmax
  rw [Nat.sub_add_cancel hm] at h
  exact h

/-! ## Reindexing lemmas -/

lemma sum_shift_odd (A : BoundingSieve) (E : ℝ) (q M : ℕ) :
    (∑ n ∈ (Finset.range M).filter (fun n : ℕ => Odd n ∧ 3 ≤ n), T A (n - 1) E q)
      = evenPosSum A E q (M - 1) := by
  unfold evenPosSum
  refine Finset.sum_nbij' (fun n => n - 1) (fun r => r + 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnM, hnodd, hn3⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_range] at hnM
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      Nat.Odd.sub_odd hnodd odd_one, by omega⟩
  · intro r hr
    obtain ⟨hrM, hrev, hr0⟩ := Finset.mem_filter.mp hr
    rw [Finset.mem_range] at hrM
    have h2 : 2 ≤ r := by obtain ⟨k, hk⟩ := hrev; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hrev.add_one, by omega⟩
  · intro n hn
    obtain ⟨hnM, hnodd, hn3⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_range] at hnM
    omega
  · intro r hr
    obtain ⟨hrM, hrev, hr0⟩ := Finset.mem_filter.mp hr
    rw [Finset.mem_range] at hrM
    omega
  · intro n _
    rfl

lemma sum_shift_even (A : BoundingSieve) (E : ℝ) (q M : ℕ) :
    (∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0), T A (n - 1) E q)
      = oddSum A E q (M - 1) := by
  unfold oddSum
  refine Finset.sum_nbij' (fun n => n - 1) (fun r => r + 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnM, hrev, hn0⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_range] at hnM
    have h1 : 1 ≤ n := by obtain ⟨k, hk⟩ := hrev; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      Nat.Even.sub_odd h1 hrev odd_one⟩
  · intro r hr
    obtain ⟨hrM, hrodd⟩ := Finset.mem_filter.mp hr
    rw [Finset.mem_range] at hrM
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hrodd.add_one, by omega⟩
  · intro n hn
    obtain ⟨hnM, hrev, hn0⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_range] at hnM
    have h1 : 1 ≤ n := by obtain ⟨k, hk⟩ := hrev; omega
    omega
  · intro r hr
    obtain ⟨hrM, hrodd⟩ := Finset.mem_filter.mp hr
    rw [Finset.mem_range] at hrM
    omega
  · intro n _
    rfl

lemma odd_restrict (A : BoundingSieve) {D : ℝ} {q : ℕ} (M : ℕ) (hM : 2 ≤ M) :
    (∑ n ∈ (Finset.range M).filter (fun n : ℕ => Odd n),
        (if Tcond n D q then A.nu q * T A (n - 1) (D / q) q else 0))
      = A.nu q * (if (q : ℝ) ^ 3 ≤ D then evenPosSum A (D / q) q (M - 1) else VfR A q) := by
  by_cases hG : (q : ℝ) ^ 3 ≤ D
  · rw [if_pos hG]
    have hiff : ∀ n, Odd n → (Tcond n D q ↔ 3 ≤ n) := by
      intro n hnodd
      constructor
      · intro hc
        by_contra h3
        have hn1 : n = 1 := by obtain ⟨k, hk⟩ := hnodd; omega
        subst hn1
        rw [Tcond_one_iff] at hc
        linarith
      · intro h3
        exact (Tcond_odd_ge_three D q (by omega) hnodd).mpr hG
    rw [show (∑ n ∈ (Finset.range M).filter (fun n : ℕ => Odd n),
            (if Tcond n D q then A.nu q * T A (n - 1) (D / q) q else 0))
        = ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Odd n),
            (if 3 ≤ n then A.nu q * T A (n - 1) (D / q) q else 0) from
      Finset.sum_congr rfl (fun n hn => by
        have hnodd := (Finset.mem_filter.mp hn).2
        by_cases h3 : 3 ≤ n
        · rw [if_pos ((hiff n hnodd).mpr h3), if_pos h3]
        · rw [if_neg (fun hc => h3 ((hiff n hnodd).mp hc)), if_neg h3])]
    rw [← Finset.sum_filter, Finset.filter_filter, ← Finset.mul_sum,
      sum_shift_odd A (D / q) q M]
  · rw [if_neg hG]
    have hDlt : D < (q : ℝ) ^ 3 := not_le.mp hG
    have hiff : ∀ n, Odd n → (Tcond n D q ↔ n = 1) := by
      intro n hnodd
      constructor
      · intro hc
        by_contra hne
        have h3 : 3 ≤ n := by obtain ⟨k, hk⟩ := hnodd; omega
        exact hG ((Tcond_odd_ge_three D q (by omega) hnodd).mp hc)
      · intro h1; subst h1; rw [Tcond_one_iff]; exact hDlt
    rw [Finset.sum_eq_single 1]
    · rw [if_pos ((hiff 1 odd_one).mpr rfl)]
      rfl
    · intro n hn hne
      exact if_neg (fun hc => hne ((hiff n (Finset.mem_filter.mp hn).2).mp hc))
    · intro h1not
      exfalso
      exact h1not (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), odd_one⟩)

lemma oddSum_split (A : BoundingSieve) {z D : ℝ} {q : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (hq : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    oddSum A D z M
      = oddSum A D q M
        + A.nu q * (if (q : ℝ) ^ 3 ≤ D then evenPosSum A (D / q) q (M - 1) else VfR A q) := by
  have e1 : oddSum A D z M
      = ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Odd n),
          (T A n D q + (if Tcond n D q then A.nu q * T A (n - 1) (D / q) q else 0)) := by
    rw [oddSum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := by
      obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hn).2; omega
    exact T_split A hn1 hq hqz hmax
  rw [e1, Finset.sum_add_distrib]
  rw [show oddSum A D q M
      = ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Odd n), T A n D q from rfl]
  rw [odd_restrict A M hM]

lemma evenPosSum_split (A : BoundingSieve) {z E : ℝ} {q : ℕ} (M : ℕ)
    (hq : q ∈ A.prodPrimes.primeFactors) (hqz : (q : ℝ) < z)
    (hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q) :
    evenPosSum A E z M
      = evenPosSum A E q M + A.nu q * oddSum A (E / q) q (M - 1) := by
  have e1 : evenPosSum A E z M
      = ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0),
          (T A n E q + A.nu q * T A (n - 1) (E / q) q) := by
    rw [evenPosSum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    obtain ⟨hnM, hrev, hn0⟩ := Finset.mem_filter.mp hn
    have h2 : 2 ≤ n := by obtain ⟨k, hk⟩ := hrev; omega
    rw [T_split A (by omega : 1 ≤ n) hq hqz hmax,
      if_pos (Tcond_even E q h2 hrev)]
  rw [e1, Finset.sum_add_distrib]
  rw [show evenPosSum A E q M
      = ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0), T A n E q from rfl]
  rw [show (∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0),
        A.nu q * T A (n - 1) (E / q) q)
      = A.nu q * oddSum A (E / q) q (M - 1) from by
        rw [← Finset.mul_sum, sum_shift_even A (E / q) q M]]

lemma oddSum_eq_of_vanishing (A : BoundingSieve) {D z : ℝ} {K M : ℕ} (hKM : K ≤ M)
    (hvan : ∀ n : ℕ, K ≤ n → T A n D z = 0) : oddSum A D z M = oddSum A D z K := by
  rw [oddSum, oddSum]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn
    obtain ⟨hnK, hnodd⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_range] at hnK
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnodd⟩
  · intro n hn hnot
    obtain ⟨hnM, hnodd⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_range] at hnM
    refine hvan n ?_
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnodd⟩)

theorem main_ind : ∀ (n₀ : ℕ), ∀ (A : BoundingSieve) (z D : ℝ) (M : ℕ),
    (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)).card = n₀ → n₀ < M →
    oddSum A D z M = Gp A z D - VfR A z ∧ evenPosSum A D z M = VfR A z - Gm A z D := by
  intro n₀
  induction n₀ using Nat.strong_induction_on with
  | _ n₀ ih =>
    intro A z D M hcard hM
    by_cases hne : (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)).Nonempty
    · set S := A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) with hSdef
      set q := S.max' hne with hqdef
      have hqS : q ∈ S := Finset.max'_mem S hne
      have hq : q ∈ A.prodPrimes.primeFactors := (Finset.mem_filter.mp hqS).1
      have hqz : (q : ℝ) < z := (Finset.mem_filter.mp hqS).2
      have hmax : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → p ≤ q :=
        fun p hp hpz => Finset.le_max' S p (Finset.mem_filter.mpr ⟨hp, hpz⟩)
      have hSins : S = insert q (primesLt A q) := primesLt_insert A hq hqz hmax
      have hqnot : q ∉ primesLt A q := not_mem_primesLt_self A q
      have hcardq : (primesLt A q).card + 1 = n₀ := by
        rw [← hcard, hSins, Finset.card_insert_of_notMem hqnot]
      have hltq : (primesLt A q).card < n₀ := by omega
      have hM1 : (primesLt A q).card < M := by omega
      have hM2 : (primesLt A q).card < M - 1 := by omega
      have hM2' : 2 ≤ M := by omega
      obtain ⟨ih1, ih2⟩ := ih (primesLt A q).card hltq A q D M rfl hM1
      obtain ⟨ih3, ih4⟩ := ih (primesLt A q).card hltq A q (D / q) (M - 1) rfl hM2
      obtain ⟨hgp, hgm, hV⟩ := Gp_Gm_split A hq hqz hmax
      constructor
      · rw [oddSum_split A M hM2' hq hqz hmax, ih1]
        by_cases hG : (q : ℝ) ^ 3 ≤ D
        · rw [if_pos hG, ih4, hgp, hV, if_pos hG]; ring
        · rw [if_neg hG, hgp, hV, if_neg hG]; ring
      · rw [evenPosSum_split A M hq hqz hmax, ih2, ih3, hgm D, hV]; ring
    · have hempty : A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      have hzp : primesLt A z = ∅ := hempty
      have hPz : Pz A z = 1 := by rw [Pz_eq_prod, hzp, Finset.prod_empty]
      have hV : VfR A z = 1 := by rw [VfR_eq_prod, hzp, Finset.prod_empty]
      have hT0 : ∀ n : ℕ, n ≠ 0 → T A n D z = 0 := by
        intro n hn
        rcases n with _ | k
        · exact absurd rfl hn
        · rw [T.eq_2 A D z k]
          apply Finset.sum_eq_zero
          intro p hp
          have hmem : p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) :=
            Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
          rw [hempty] at hmem
          exact absurd hmem (Finset.notMem_empty p)
      have hodd0 : oddSum A D z M = 0 := by
        rw [oddSum]
        apply Finset.sum_eq_zero
        intro n hn
        exact hT0 n (fun h0 => by rw [h0] at hn; simp at hn)
      have hev0 : evenPosSum A D z M = 0 := by
        rw [evenPosSum]
        apply Finset.sum_eq_zero
        intro n hn
        exact hT0 n (Finset.mem_filter.mp hn).2.2
      have hGp1 : Gp A z D = 1 := by
        rw [Gp, hPz]
        rw [Nat.divisors_one, Finset.sum_singleton]
        have hrd : rdPlus D 1 := by
          intro e he hodd
          rw [Nat.mem_divisors] at he
          have he1 : e = 1 := Nat.dvd_one.mp he.1
          subst he1
          simp at hodd
        rw [if_pos hrd, ArithmeticFunction.moebius_apply_one, A.nu_mult.1]
        norm_num
      have hGm1 : Gm A z D = 1 := by
        rw [Gm, hPz]
        rw [Nat.divisors_one, Finset.sum_singleton]
        have hrd : rdMinus D 1 := by
          intro e he _ he1
          rw [Nat.mem_divisors] at he
          exact absurd (Nat.dvd_one.mp he.1) he1
        rw [if_pos hrd, ArithmeticFunction.moebius_apply_one, A.nu_mult.1]
        norm_num
      rw [hodd0, hev0, hGp1, hGm1, hV]
      norm_num

theorem identity_plus (A : BoundingSieve) {D z : ℝ} (hD : 1 ≤ D) :
    ∑ d ∈ (Pz A z).divisors, lamPlus A.prodPrimes D d * A.nu d
      = VfR A z
        + ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n), T A n D z := by
  set K := Nat.log 2 ⌈D⌉₊ + 3 with hKdef
  have hvan : ∀ n : ℕ, K ≤ n → T A n D z = 0 := by
    intro n hn
    by_contra hne
    have h3 : 3 ≤ n := by omega
    have hb := T_ne_zero_le h3 hne
    have hKl : Nat.log 2 ⌈D⌉₊ + 1 ≤ n - 2 := by omega
    have hp : (2 : ℝ) ^ (Nat.log 2 ⌈D⌉₊ + 1) ≤ (2 : ℝ) ^ (n - 2) :=
      pow_le_pow_right₀ (by norm_num) hKl
    have hlt : (⌈D⌉₊ : ℝ) < (2 : ℝ) ^ (Nat.log 2 ⌈D⌉₊ + 1) := by
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌈D⌉₊
      exact_mod_cast h
    have hle : D ≤ (⌈D⌉₊ : ℝ) := Nat.le_ceil D
    linarith
  set N := A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) with hNdef
  have hbig : N.card < K + N.card + 1 := by omega
  obtain ⟨hodd, -⟩ := main_ind N.card A z D (K + N.card + 1) rfl hbig
  have hsum : oddSum A D z (K + N.card + 1) = oddSum A D z K :=
    oddSum_eq_of_vanishing A (by omega) hvan
  have hGpeq : (∑ d ∈ (Pz A z).divisors, lamPlus A.prodPrimes D d * A.nu d) = Gp A z D := by
    rw [Gp]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdvd : d ∣ A.prodPrimes := dvd_trans (Nat.mem_divisors.mp hd).1 (Pz_dvd_prodPrimes A z)
    rw [lamPlus]
    by_cases hr : rdPlus D d
    · rw [if_pos ⟨hdvd, hr⟩, if_pos hr]
    · rw [if_neg (fun hc => hr hc.2), if_neg hr]
  rw [hGpeq]
  have hfinal : Gp A z D = VfR A z + oddSum A D z K := by
    rw [← hsum]
    linarith
  rw [hfinal, oddSum]

end

end Work.ChenPlan.LinearSieve.RI
