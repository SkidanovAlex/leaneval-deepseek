import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.ChenPlan.H2.Defs
import Submission.Work.ChenPlan.H2.RemSumQ
import Submission.Work.ChenPlan.H2.window_Ut_sum_le
import Submission.Work.NumberTheory.Chen.mertens_lower_tenth
import Submission.Work.ChenPlan.H2.vsieve_ratio_lower_int
import Submission.Work.ChenPlan.H2.prod_odd_range_eq_vsieve
import Submission.Commons.NumberTheory.Mertens.sum_log_div_le_log_sharp

/-!
# Chen's `h2` from the upper linear sieve, against the 2026-09-24 v6 interface

The body below is the v5 proof of `Submission/Work/ChenPlan/H2/h2_of_sieve_two.lean`, which no longer
compiles because `Submission.ChenPlan.LinearSieveUpper` (v6) carries one more hypothesis on the sieve
problem, Richert's two-sided dimension condition `IsLinearMertens s z K`.  Only the places where the
sieve is applied are changed:

* `apMass_le_main_add_rem_v6` : the per-`q` sieve bound with the extra hypothesis threaded through;
* `isLinearMertens_apSieve` : `IsLinearMertens` for `apSieve x M q` with a constant independent of
  `x, M, q`, from `oddPrimLt_mertens_bound` — Mertens' first theorem for the density
  `ν(p) = 1/(p-1)`, a two-point difference of the sharp form
  `Commons.NumberTheory.Mertens.sum_log_div_le_log_sharp`; `IsLinearMertens_mono` raises the
  constant to the running maximum.
* `oddPrimLt_mertens_bound` : that Mertens bound for the odd primes below `M`, proved here (with
  the helpers `primePredLogSum`, `primePredLogSum_bound`, `primesLE_filter_not_le`,
  `primePredLogSum_split`, `invTotient_mul_log_eq`).
-/

open Finset Filter
open scoped BigOperators

namespace Work.ChenPlan.H2

noncomputable section

open Commons.NumberTheory.Chen.ChenEight
open Commons.NumberTheory.Chen (Vsieve Vsieve_pos Vsieve_mono vsieve_log_lower_sharp)

open Work.ChenPlan.H1 (invTotient invTotient_apply)


/-! ## The range constant -/

/-- The constant `K` of `IsLinearRange` for the sieve problem `apSieve`.  `log (4/3)` is the slack
in `log ⌈z'⌉ ≤ log z' + log (4/3)` (valid for `z' ≥ 3`); the `+ 1`, multiplied by `log z' ≥ 1`
below, absorbs the `+ 1` in `⌈z'⌉ ≤ z' + 1`. -/
def rangeK (K : ℝ) : ℝ := K + Real.log (4 / 3) * (1 + K) + 1

lemma rangeK_nonneg {K : ℝ} (hK : 0 ≤ K) : 0 ≤ rangeK K := by
  have h1 : 0 ≤ Real.log (4 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ 1 + K := by linarith
  rw [rangeK]
  nlinarith [mul_nonneg h1 h3]

lemma le_rangeK {K : ℝ} (hK : 0 ≤ K) : K ≤ rangeK K := by
  have h1 : 0 ≤ Real.log (4 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ 1 + K := by linarith
  rw [rangeK]
  nlinarith [mul_nonneg h1 h3]

/-! ## Elementary arithmetic of the range reduction -/

/-- The core inequality behind the range version: if `A ≤ B`, `1 ≤ B`, `K ≥ 0` and
`C ≤ B + log(4/3)` then `C (A + K) ≤ B (A + rangeK K)`. -/
lemma key_le {A B C K : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hB1 : 1 ≤ B) (hC : C ≤ B + Real.log (4 / 3)) (hK : 0 ≤ K) :
    C * (A + K) ≤ B * (A + rangeK K) := by
  have hlam : 0 ≤ Real.log (4 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have h1 : C * (A + K) ≤ (B + Real.log (4 / 3)) * (A + K) :=
    mul_le_mul_of_nonneg_right hC (by linarith)
  have h4 : Real.log (4 / 3) * A ≤ Real.log (4 / 3) * B := mul_le_mul_of_nonneg_left hAB hlam
  have h6 : Real.log (4 / 3) * K ≤ B * (Real.log (4 / 3) * K) + B := by
    have h := mul_le_mul_of_nonneg_right hB1 (mul_nonneg hlam hK)
    linarith
  rw [rangeK]
  nlinarith [h1, h4, h6, hA, hK, hlam]

/-- Division form of `key_le`. -/
lemma div_ratio_le {A B C K : ℝ} (hA : 0 < A) (h : C * (A + K) ≤ B * (A + rangeK K)) :
    (C / A) * (1 + K / A) ≤ (B / A) * (1 + rangeK K / A) := by
  have e1 : (C / A) * (1 + K / A) = C * (A + K) / A ^ 2 := by field_simp
  have e2 : (B / A) * (1 + rangeK K / A) = B * (A + rangeK K) / A ^ 2 := by field_simp
  rw [e1, e2, div_le_div_iff_of_pos_right (by positivity)]
  exact h

/-! ## Two elementary facts about the prime factors of `oddPrimLt M` -/

lemma primeFactors_oddPrimLt_eq_oddLt (M : ℕ) : (oddPrimLt M).primeFactors = oddLt M := by
  rw [oddPrimLt_eq_prod_oddLt]
  exact Nat.primeFactors_prod (fun p hp => (Submission.mem_oddLt.mp hp).1)

/-- The prime factors of `oddPrimLt M` are the primes `3 ≤ p < M`. -/
lemma prime_odd_of_mem_primeFactors_oddPrimLt {p M : ℕ}
    (hp : p ∈ (oddPrimLt M).primeFactors) : p.Prime ∧ 3 ≤ p ∧ p < M := by
  rw [primeFactors_oddPrimLt_eq_oddLt M] at hp
  rw [show oddLt M = (Finset.range M).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p) from rfl] at hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨hp.2.1, hp.2.2, hp.1⟩

/-- Conversely, a prime `3 ≤ p < X` is a prime factor of `oddPrimLt X`. -/
lemma mem_primeFactors_oddPrimLt {p X : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hpX : p < X) :
    p ∈ (oddPrimLt X).primeFactors := by
  rw [primeFactors_oddPrimLt_eq_oddLt X]
  rw [show oddLt X = (Finset.range X).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p) from rfl]
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨hpX, hp, hp3⟩


/-! ## Mertens' first theorem for the density `ν(p) = 1/(p-1)` on the odd primes

The extra hypothesis of the v6 sieve interface, Richert's `Ω₁ + Ω₂(1,L)` condition
`IsLinearMertens s z K`, has to be discharged for the per-`q` sieve problem `apSieve x M q`, whose
sifting primes are the odd primes below `M` with density `ν(p) = 1/(p-1)`.

The estimate is a two-point difference of the sharp form of Mertens' first theorem for `log p/(p-1)`
(`Commons.NumberTheory.Mertens.sum_log_div_le_log_sharp`): there is `A > 0` with
`|Σ_{p ≤ y} log p/(p-1) - log y| ≤ A` for every integer `y ≥ 2`.  For `2 ≤ w < z'` the sum
`Σ_{w ≤ p < z'} log p/(p-1)` over odd primes equals `Σ_{p ≤ z''} - Σ_{p ≤ u}` where
`z'' = ⌈z'⌉₊ - 1` is the largest integer `< z'` and `u = max ⌈w⌉₊ 3 - 1` is the largest integer
`< max ⌈w⌉₊ 3`; the two evaluation points are within a factor `3/2` of `z'` resp. a factor `2` of
`w`, and the `p = 2` term cancels in the difference. -/

/-- `Σ_{p ≤ n} log p/(p-1)`: the cumulative sum of the sieve density `ν(p) = 1/(p-1)` over the
primes `p ≤ n` (including `p = 2`, which cancels in differences). -/
noncomputable def primePredLogSum (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, Real.log (p : ℝ) / ((p : ℝ) - 1)

/-- Mertens' bound for the cumulative prime pred-sum, from the filtered form. -/
lemma primePredLogSum_bound {A : ℝ}
    (hA : ∀ y : ℕ, 2 ≤ y →
      |(∑ p ∈ (Nat.primesLE y).filter (fun p : ℕ => 2 ≤ p),
          Real.log (p : ℝ) / ((p : ℝ) - 1)) - Real.log (y : ℝ)| ≤ A)
    {n : ℕ} (hn : 2 ≤ n) : |primePredLogSum n - Real.log (n : ℝ)| ≤ A := by
  have hf : (Nat.primesLE n).filter (fun p : ℕ => 2 ≤ p) = Nat.primesLE n :=
    Finset.filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2.two_le)
  rw [primePredLogSum, ← hf]
  exact hA n hn

/-- The primes `≤ n` that are below `u` are the primes `≤ u - 1`. -/
lemma primesLE_filter_not_le {n u : ℕ} (hu1 : 1 ≤ u) (hun : u ≤ n + 1) :
    (Nat.primesLE n).filter (fun p : ℕ => ¬ (u ≤ p)) = Nat.primesLE (u - 1) := by
  have h1 : (Nat.primesLE n).filter (fun p : ℕ => ¬ (u ≤ p))
      = (Nat.primesLE n).filter (fun p : ℕ => p < u) := by
    refine Finset.filter_congr ?_
    intro p _
    exact not_le
  rw [h1]
  ext p
  simp only [Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpn, hpp⟩, hpu⟩
    exact ⟨by omega, hpp⟩
  · rintro ⟨hple, hpp⟩
    exact ⟨⟨by omega, hpp⟩, by omega⟩

/-- Splitting the cumulative prime pred-sum at `u`: `Σ_{p ≤ n} = Σ_{p < u} + Σ_{u ≤ p ≤ n}`. -/
lemma primePredLogSum_split {n u : ℕ} (hu1 : 1 ≤ u) (hun : u ≤ n + 1) :
    primePredLogSum n = primePredLogSum (u - 1)
      + ∑ p ∈ (Nat.primesLE n).filter (fun p => u ≤ p),
          Real.log (p : ℝ) / ((p : ℝ) - 1) := by
  have h := Finset.sum_filter_add_sum_filter_not (Nat.primesLE n) (fun p : ℕ => u ≤ p)
    (fun p : ℕ => Real.log (p : ℝ) / ((p : ℝ) - 1))
  rw [primesLE_filter_not_le hu1 hun] at h
  rw [primePredLogSum, primePredLogSum]
  linarith

/-- `ν(p) log p = log p/(p-1)` at a prime, for `ν = invTotient = 1/φ`. -/
lemma invTotient_mul_log_eq {p : ℕ} (hp : p.Prime) :
    invTotient p * Real.log (p : ℝ) = Real.log (p : ℝ) / ((p : ℝ) - 1) := by
  have h1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le]; push_cast; ring
  rw [invTotient_apply, Nat.totient_prime hp, h1, inv_eq_one_div]
  ring

/-- **Mertens' first theorem for the density `ν(p) = 1/(p-1)` on the odd primes below `M`** — the
second conjunct of `IsLinearMertens` for the sieve problem `apSieve x M q`. -/
theorem oddPrimLt_mertens_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℕ) (w z' : ℝ), 2 ≤ w → w < z' → z' ≤ (M : ℝ) →
      |(∑ p ∈ (oddPrimLt M).primeFactors.filter
            (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
          invTotient p * Real.log (p : ℝ)) - Real.log (z' / w)| ≤ K := by
  obtain ⟨A, hApos, hA⟩ := Commons.NumberTheory.Mertens.sum_log_div_le_log_sharp
  have hA0 : 0 ≤ A := le_of_lt hApos
  refine ⟨2 * A + Real.log (3 / 2) + Real.log 2 + 1, by positivity, ?_⟩
  intro M w z' hw hwz hz'M
  have hwpos : (0 : ℝ) < w := by linarith
  have hz'pos : (0 : ℝ) < z' := by linarith
  have hz'2 : (2 : ℝ) < z' := by linarith
  have hlog32 : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- the two integer evaluation points
  have hz'3 : 3 ≤ ⌈z'⌉₊ := by
    have h : 2 < ⌈z'⌉₊ := Nat.lt_ceil.mpr hz'2
    omega
  have hw2 : 2 ≤ ⌈w⌉₊ := by
    have h : (2 : ℝ) ≤ (⌈w⌉₊ : ℝ) := le_trans hw (Nat.le_ceil w)
    exact_mod_cast h
  have huz : max ⌈w⌉₊ 3 ≤ ⌈z'⌉₊ := max_le (Nat.ceil_mono (le_of_lt hwz)) hz'3
  have h3u : 3 ≤ max ⌈w⌉₊ 3 := le_max_right _ _
  have huw : ⌈w⌉₊ ≤ max ⌈w⌉₊ 3 := le_max_left _ _
  have hnz2 : 2 ≤ ⌈z'⌉₊ - 1 := by omega
  have hu2 : 2 ≤ max ⌈w⌉₊ 3 - 1 := by omega
  -- the sifted range is the primes in `[max ⌈w⌉₊ 3, ⌈z'⌉₊ - 1]`
  have hset : (oddPrimLt M).primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z')
      = (Nat.primesLE (⌈z'⌉₊ - 1)).filter (fun p : ℕ => max ⌈w⌉₊ 3 ≤ p) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨hp, hwp, hpz⟩
      obtain ⟨hpp, hp3, _⟩ := prime_odd_of_mem_primeFactors_oddPrimLt hp
      have hplt : p < ⌈z'⌉₊ := Nat.lt_ceil.mpr hpz
      exact ⟨⟨by omega, hpp⟩, max_le (Nat.ceil_le.mpr hwp) hp3⟩
    · rintro ⟨⟨hple, hpp⟩, hup⟩
      have hp3 : 3 ≤ p := le_trans h3u hup
      have hpw : w ≤ (p : ℝ) :=
        le_trans (Nat.le_ceil w) (by exact_mod_cast (le_trans huw hup))
      have hpz : (p : ℝ) < z' := Nat.lt_ceil.mp (by omega)
      have hpM : p < M := by
        have h : (p : ℝ) < (M : ℝ) := lt_of_lt_of_le hpz hz'M
        exact_mod_cast h
      exact ⟨mem_primeFactors_oddPrimLt hpp hp3 hpM, hpw, hpz⟩
  have hsum : (∑ p ∈ (oddPrimLt M).primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'), invTotient p * Real.log (p : ℝ))
      = ∑ p ∈ (Nat.primesLE (⌈z'⌉₊ - 1)).filter (fun p : ℕ => max ⌈w⌉₊ 3 ≤ p),
          Real.log (p : ℝ) / ((p : ℝ) - 1) := by
    rw [hset]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    exact invTotient_mul_log_eq ((Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2)
  -- the value of the sum
  have hS : (∑ p ∈ (Nat.primesLE (⌈z'⌉₊ - 1)).filter (fun p : ℕ => max ⌈w⌉₊ 3 ≤ p),
        Real.log (p : ℝ) / ((p : ℝ) - 1))
      = primePredLogSum (⌈z'⌉₊ - 1) - primePredLogSum (max ⌈w⌉₊ 3 - 1) := by
    have hsp := primePredLogSum_split (n := ⌈z'⌉₊ - 1) (u := max ⌈w⌉₊ 3) (by omega) (by omega)
    linarith [hsp]
  -- the two evaluation points sit close to `z'` and `w`
  have hz''1 : 1 ≤ ⌈z'⌉₊ := by omega
  have hc1 : ((⌈z'⌉₊ : ℕ) : ℝ) = ((⌈z'⌉₊ - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hz''1]; push_cast; ring
  have hnz_le : ((⌈z'⌉₊ - 1 : ℕ) : ℝ) ≤ z' := by
    have h : ((⌈z'⌉₊ : ℕ) : ℝ) < z' + 1 := Nat.ceil_lt_add_one hz'pos.le
    linarith
  have hz'_le : z' ≤ ((⌈z'⌉₊ - 1 : ℕ) : ℝ) + 1 := by
    have h : z' ≤ ((⌈z'⌉₊ : ℕ) : ℝ) := Nat.le_ceil z'
    linarith
  have hnzpos : (0 : ℝ) < ((⌈z'⌉₊ - 1 : ℕ) : ℝ) := by
    have : (0 : ℕ) < ⌈z'⌉₊ - 1 := by omega
    exact_mod_cast this
  have hnear1 : |Real.log ((⌈z'⌉₊ - 1 : ℕ) : ℝ) - Real.log z'| ≤ Real.log (3 / 2) := by
    have hratio : z' / ((⌈z'⌉₊ - 1 : ℕ) : ℝ) ≤ 3 / 2 := by
      rw [div_le_iff₀ hnzpos]
      have h2 : (2 : ℝ) ≤ ((⌈z'⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast hnz2
      nlinarith [hz'_le, h2]
    have hlogeq : Real.log z' - Real.log ((⌈z'⌉₊ - 1 : ℕ) : ℝ)
        = Real.log (z' / ((⌈z'⌉₊ - 1 : ℕ) : ℝ)) :=
      (Real.log_div (ne_of_gt hz'pos) (ne_of_gt hnzpos)).symm
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hnzpos hnz_le)), hlogeq]
    exact Real.log_le_log (div_pos hz'pos hnzpos) hratio
  have hu_ceil : max ⌈w⌉₊ 3 ≤ ⌈w⌉₊ + 1 := max_le (by omega) (by omega)
  have hmpos : (0 : ℝ) < ((max ⌈w⌉₊ 3 - 1 : ℕ) : ℝ) := by
    have : (0 : ℕ) < max ⌈w⌉₊ 3 - 1 := by omega
    exact_mod_cast this
  have hm_le_2w : ((max ⌈w⌉₊ 3 - 1 : ℕ) : ℝ) ≤ 2 * w := by
    have h1 : ((max ⌈w⌉₊ 3 - 1 : ℕ) : ℝ) ≤ ((max ⌈w⌉₊ 3 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    have h2 : ((max ⌈w⌉₊ 3 : ℕ) : ℝ) ≤ ((⌈w⌉₊ : ℕ) : ℝ) + 1 := by exact_mod_cast hu_ceil
    have h3 : ((⌈w⌉₊ : ℕ) : ℝ) < w + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hw_le_2m : w ≤ 2 * ((max ⌈w⌉₊ 3 - 1 : ℕ) : ℝ) := by
    have h1 : ((⌈w⌉₊ : ℕ) : ℝ) ≤ ((max ⌈w⌉₊ 3 : ℕ) : ℝ) := by exact_mod_cast huw
    have h2 : ((max ⌈w⌉₊ 3 - 1 : ℕ) : ℝ) + 1 = ((max ⌈w⌉₊ 3 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ max ⌈w⌉₊ 3)]; ring
    have h3 : (2 : ℝ) ≤ ((max ⌈w⌉₊ 3 - 1 : ℕ) : ℝ) := by exact_mod_cast hu2
    have h4 : w ≤ ((⌈w⌉₊ : ℕ) : ℝ) := Nat.le_ceil w
    linarith
  have hnear2 : |Real.log ((max ⌈w⌉₊ 3 - 1 : ℕ) : ℝ) - Real.log w| ≤ Real.log 2 := by
    rw [abs_le]
    constructor
    · have h := Real.log_le_log hwpos hw_le_2m
      rw [Real.log_mul (by norm_num) (ne_of_gt hmpos)] at h
      linarith
    · have h := Real.log_le_log hmpos hm_le_2w
      rw [Real.log_mul (by norm_num) (ne_of_gt hwpos)] at h
      linarith
  -- assemble
  have hmain : |(∑ p ∈ (oddPrimLt M).primeFactors.filter
            (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
          invTotient p * Real.log (p : ℝ)) - Real.log (z' / w)|
      ≤ 2 * A + Real.log (3 / 2) + Real.log 2 := by
    rw [hsum, hS, Real.log_div (ne_of_gt hz'pos) (ne_of_gt hwpos)]
    have hkey : primePredLogSum (⌈z'⌉₊ - 1) - primePredLogSum (max ⌈w⌉₊ 3 - 1)
          - (Real.log z' - Real.log w)
        = (primePredLogSum (⌈z'⌉₊ - 1) - Real.log ((⌈z'⌉₊ - 1 : ℕ) : ℝ))
          - (primePredLogSum (max ⌈w⌉₊ 3 - 1) - Real.log ((max ⌈w⌉₊ 3 - 1 : ℕ) : ℝ))
          + (Real.log ((⌈z'⌉₊ - 1 : ℕ) : ℝ) - Real.log z')
          - (Real.log ((max ⌈w⌉₊ 3 - 1 : ℕ) : ℝ) - Real.log w) := by ring
    rw [hkey]
    obtain ⟨ha1, ha2⟩ := abs_le.mp (primePredLogSum_bound hA hnz2)
    obtain ⟨hb1, hb2⟩ := abs_le.mp (primePredLogSum_bound hA hu2)
    obtain ⟨hc1, hc2⟩ := abs_le.mp hnear1
    obtain ⟨hd1, hd2⟩ := abs_le.mp hnear2
    refine abs_le.mpr ⟨by linarith, by linarith⟩
  linarith [hmain]

/-! ## The range form of the dimension bound for `apSieve` -/

/-- **The range dimension bound for the sieve product**, from the Mertens ratio `hrate` at
integer limits: for `2 ≤ w < z'` the product over the odd primes of `[w, z')` is at most
`(log z'/log w)(1 + rangeK K/log w)`. -/
lemma prod_sieve_le_range {K : ℝ} (hK : 0 ≤ K) {M : ℕ} {w z' : ℝ}
    (hw : 2 ≤ w) (hwz : w < z') (_hz'M : z' ≤ (M : ℝ))
    (hrate : ∀ (z : ℕ) (wt : ℝ), 2 ≤ wt → wt < z →
      (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ wt ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)))
        ≤ (Real.log (z : ℝ) / Real.log wt) * (1 + K / Real.log wt)) :
    (∏ p ∈ (oddPrimLt M).primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'), (1 - invTotient p)⁻¹)
      ≤ (Real.log z' / Real.log w) * (1 + rangeK K / Real.log w) := by
  have hw1 : (1 : ℝ) < w := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  by_cases hz3 : z' ≤ 3
  · -- the product is empty
    have hempty : (oddPrimLt M).primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z') = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp hP
      obtain ⟨hpp, hp3, -⟩ := prime_odd_of_mem_primeFactors_oddPrimLt hp
      obtain ⟨-, hpz⟩ := hP
      have h3p : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      linarith
    rw [hempty, Finset.prod_empty]
    have hlogw_le : Real.log w ≤ Real.log z' := Real.log_le_log (by linarith) (le_of_lt hwz)
    have h1 : (1 : ℝ) ≤ Real.log z' / Real.log w := by
      rw [le_div_iff₀ hlogw]; linarith
    have h2 : (1 : ℝ) ≤ 1 + rangeK K / Real.log w := by
      have h := rangeK_nonneg hK
      have : 0 ≤ rangeK K / Real.log w := div_nonneg h hlogw.le
      linarith
    have h3 : (0 : ℝ) ≤ Real.log z' / Real.log w := le_trans zero_le_one h1
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (Real.log z' / Real.log w) * (1 + rangeK K / Real.log w) :=
          mul_le_mul h1 h2 (by norm_num) h3
  · push_neg at hz3
    set n : ℕ := ⌈z'⌉₊ with hn
    have hz'n : z' ≤ (n : ℝ) := by rw [hn]; exact Nat.le_ceil z'
    have h3n : 3 < n := by
      rw [hn]; exact Nat.lt_ceil.mpr (by exact_mod_cast hz3)
    have hwn : w < (n : ℝ) := lt_of_lt_of_le hwz hz'n
    -- the odd primes of `[w, z')` are among the odd primes of `[w, n)`
    have hsub : (oddPrimLt M).primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z')
        ⊆ (oddPrimLt n).primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      obtain ⟨hpmem, hwp, hpz⟩ := hp
      obtain ⟨hpp, hp3, -⟩ := prime_odd_of_mem_primeFactors_oddPrimLt hpmem
      have hpn : p < n := by
        have : (p : ℝ) < (n : ℝ) := lt_of_lt_of_le hpz hz'n
        exact_mod_cast this
      exact ⟨mem_primeFactors_oddPrimLt hpp hp3 hpn, hwp⟩
    have h1f : ∀ i ∈ (oddPrimLt M).primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'), 0 ≤ (1 - invTotient i)⁻¹ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpp, hp3, -⟩ := prime_odd_of_mem_primeFactors_oddPrimLt hp.1
      have hp2 : p ≠ 2 := by omega
      rw [one_sub_invTotient_inv hpp hp2]
      have h3p : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      apply div_nonneg <;> linarith
    have h2f : ∀ i ∈ (oddPrimLt n).primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)),
        i ∉ (oddPrimLt M).primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z') → 1 ≤ (1 - invTotient i)⁻¹ := by
      intro p hp _
      rw [Finset.mem_filter] at hp
      obtain ⟨hpp, hp3, -⟩ := prime_odd_of_mem_primeFactors_oddPrimLt hp.1
      have hp2 : p ≠ 2 := by omega
      rw [one_sub_invTotient_inv hpp hp2]
      have h3p : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 2)]
      linarith
    have hprod_le := Finset.prod_le_prod_of_subset_of_one_le₀ hsub h1f h2f
    have hratio := prod_ratio_le hK (by omega : 4 ≤ n) hw hwn hrate
    have hlog3_ge1 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact le_of_lt Real.exp_one_lt_three
    have hA : 0 < Real.log w := hlogw
    have hAB : Real.log w ≤ Real.log z' := Real.log_le_log (by linarith) (le_of_lt hwz)
    have hB1 : 1 ≤ Real.log z' :=
      le_trans hlog3_ge1 (Real.log_le_log (by norm_num) (le_of_lt hz3))
    have hn_le : (n : ℝ) ≤ (4 / 3) * z' := by
      have hz'pos : (0 : ℝ) ≤ z' := by linarith
      have hn1 : (n : ℝ) < z' + 1 := by rw [hn]; exact Nat.ceil_lt_add_one hz'pos
      have h2 : z' + 1 ≤ (4 / 3) * z' := by linarith
      linarith
    have hC : Real.log (n : ℝ) ≤ Real.log z' + Real.log (4 / 3) := by
      have h1 : Real.log (n : ℝ) ≤ Real.log ((4 / 3) * z') :=
        Real.log_le_log (by positivity) hn_le
      rw [Real.log_mul (by norm_num) (by linarith : z' ≠ 0)] at h1
      linarith
    have hkey : (Real.log (n : ℝ) / Real.log w) * (1 + K / Real.log w)
        ≤ (Real.log z' / Real.log w) * (1 + rangeK K / Real.log w) :=
      div_ratio_le hA (key_le hA hAB hB1 hC hK)
    exact hprod_le.trans (hratio.trans hkey)

/-- The Mertens ratio hypothesis is monotone in the constant. -/
lemma hrate_mono {K K' : ℝ} (hKle : K ≤ K')
    (hrate : ∀ (z : ℕ) (wt : ℝ), 2 ≤ wt → wt < z →
      (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ wt ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)))
        ≤ (Real.log (z : ℝ) / Real.log wt) * (1 + K / Real.log wt)) :
    ∀ (z : ℕ) (wt : ℝ), 2 ≤ wt → wt < z →
      (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ wt ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)))
        ≤ (Real.log (z : ℝ) / Real.log wt) * (1 + K' / Real.log wt) := by
  intro z wt h2 hz
  have hlogwt : 0 < Real.log wt := Real.log_pos (by linarith)
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by
    have : (2 : ℝ) ≤ (z : ℝ) := le_trans h2 (le_of_lt hz)
    linarith
  have hlogz : 0 ≤ Real.log (z : ℝ) := Real.log_nonneg hz1
  refine (hrate z wt h2 hz).trans
    (mul_le_mul_of_nonneg_left ?_ (div_nonneg hlogz hlogwt.le))
  have h : K / Real.log wt ≤ K' / Real.log wt := div_le_div_of_nonneg_right hKle hlogwt.le
  linarith

/-- **`IsLinearRange` for the sieve problem of the residue class `q`**, with the raised
constant `rangeK K`. -/
lemma isLinearRange_apSieve (x M q : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hrate : ∀ (z : ℕ) (wt : ℝ), 2 ≤ wt → wt < z →
      (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ wt ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)))
        ≤ (Real.log (z : ℝ) / Real.log wt) * (1 + K / Real.log wt)) :
    Submission.ChenPlan.IsLinearRange (apSieve x M q) (M : ℝ) (rangeK K) := by
  intro w z' hw hwz hz'M
  simp only [apSieve_prodPrimes, apSieve_nu]
  exact prod_sieve_le_range hK hw hwz hz'M hrate

/-! ## Monotonicity of the interface predicates in the sieve constant

`IsLinear` and `IsLinearRange` are monotone in `K` (a larger constant only enlarges the right-hand
side), and `IsLinearLower` is *downward* closed in `K` (a larger constant only shrinks the
left-hand side).  Hence, since `LinearSieveUpper` is quantified over every `K`, we may run the sieve
with the maximum of all constants the three instantiation lemmas require. -/

lemma IsLinear_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinear s z K) (hKK' : K ≤ K') :
    Submission.ChenPlan.IsLinear s z K' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun w hw hwz => ?_⟩
  refine (h2 w hw hwz).trans ?_
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hnn : 0 ≤ Real.log z / Real.log w := div_nonneg hlogz.le hlogw.le
  have hle : 1 + K / Real.log w ≤ 1 + K' / Real.log w := by
    have := div_le_div_of_nonneg_right hKK' hlogw.le
    linarith
  exact mul_le_mul_of_nonneg_left hle hnn

lemma IsLinearRange_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearRange s z K) (hKK' : K ≤ K') :
    Submission.ChenPlan.IsLinearRange s z K' := by
  intro w z' hw hwz hz'z
  refine (h w z' hw hwz hz'z).trans ?_
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
  have hnn : 0 ≤ Real.log z' / Real.log w := div_nonneg hlogz'.le hlogw.le
  have hle : 1 + K / Real.log w ≤ 1 + K' / Real.log w := by
    have := div_le_div_of_nonneg_right hKK' hlogw.le
    linarith
  exact mul_le_mul_of_nonneg_left hle hnn

lemma IsLinearLower_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearLower s z K) (hKK' : K ≤ K') :
    Submission.ChenPlan.IsLinearLower s z K' := by
  intro w z' hw hwz hz'z
  refine le_trans ?_ (h w z' hw hwz hz'z)
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hnn : 0 ≤ Real.log z' / Real.log w := div_nonneg (Real.log_nonneg (by linarith)) hlogw.le
  have hle : 1 - K' / Real.log w ≤ 1 - K / Real.log w := by
    have := div_le_div_of_nonneg_right hKK' hlogw.le
    linarith
  exact mul_le_mul_of_nonneg_left hle hnn

/-! ## The lower dimension bound for the sieve product

The lower half of the Mertens ratio is the mirror image of `prod_sieve_le_range`: at integer limits
it follows from the two-sided two-scale estimate `Vsieve_mul_log_diff_le` together with the sharp
lower bound `Vsieve n · log n ≥ 7/10`, and the reduction from a real range `[w, z')` to the integer
limits `s = max ⌈w⌉ 3`, `t = ⌈z'⌉` uses `log ⌈w⌉ ≤ log w + 1/w` and `z' ≤ ⌈z'⌉`. -/

lemma IsLinearMertens_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearMertens s z K) (hKK' : K ≤ K') :
    Submission.ChenPlan.IsLinearMertens s z K' := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, fun w z' hw hwz hz'z => le_trans (h2 w z' hw hwz hz'z) hKK'⟩

/-- **`IsLinearMertens` for the sieve problem `apSieve x M q`**, with a constant independent of
`x, M, q`: the density `ν = invTotient = 1/φ` is at most `1/2` at every odd prime (there
`1/φ(p) = 1/(p-1) <= 1/2` for `p >= 3`), and the log-weighted sum of the density over a range
`[w, z')` is `log (z'/w) + O(1)` by `mertens_odd_prime_log_bound` (Mertens' first theorem for
the density `ν(p) = 1/(p-1)`). -/
lemma isLinearMertens_apSieve (x M q : ℕ) {K : ℝ}
    (hMert : ∀ (M : ℕ) (w z' : ℝ), 2 ≤ w → w < z' → z' ≤ (M : ℝ) →
      |(∑ p ∈ (oddPrimLt M).primeFactors.filter
            (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
          invTotient p * Real.log (p : ℝ)) - Real.log (z' / w)| ≤ K) :
    Submission.ChenPlan.IsLinearMertens (apSieve x M q) (M : ℝ) K := by
  constructor
  · intro p hp
    rw [apSieve_prodPrimes] at hp
    simp only [apSieve_nu]
    obtain ⟨hpp, hp3, -⟩ := prime_odd_of_mem_primeFactors_oddPrimLt hp
    rw [invTotient_apply, Nat.totient_prime hpp, Nat.cast_sub hpp.one_le]
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have h2 : (2 : ℝ) ≤ (p : ℝ) - ((1 : ℕ) : ℝ) := by push_cast; linarith
    simpa [one_div] using inv_anti₀ (show (0 : ℝ) < 2 by norm_num) h2
  · intro w z' hw hwz hz'M
    simp only [apSieve_nu, apSieve_prodPrimes]
    exact hMert M w z' hw hwz hz'M

/-- The algebra of the range reduction for the lower bound: if `0 ≤ T ≤ Lt`, `0 < W ≤ Ls`,
`Ls ≤ W(1+ε)`, `0 ≤ c ≤ W` and `c + εW ≤ K`, then
`(T/W)(1 - K/W) ≤ (Lt/Ls)(1 - c/Ls)`. -/
lemma lower_key_step {T W Lt Ls K c ε : ℝ}
    (hT : 0 ≤ T) (hW : 0 < W) (hLs : 0 < Ls) (hTLt : T ≤ Lt)
    (hWLs : W ≤ Ls) (hLsW : Ls ≤ W * (1 + ε))
    (hε : 0 ≤ ε) (hc0 : 0 ≤ c) (hcW : c ≤ W) (hKW : c + ε * W ≤ K) :
    T / W * (1 - K / W) ≤ Lt / Ls * (1 - c / Ls) := by
  have hLt0 : 0 ≤ Lt := le_trans hT hTLt
  have hWe : 0 < 1 + ε := by linarith
  have hfac : 1 - ε ≤ 1 / (1 + ε) := by
    rw [le_div_iff₀ hWe]
    nlinarith
  have h1 : T / W * (1 - ε) ≤ Lt / Ls :=
    calc T / W * (1 - ε) ≤ T / W * (1 / (1 + ε)) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = T / (W * (1 + ε)) := by field_simp
      _ ≤ Lt / (W * (1 + ε)) := div_le_div_of_nonneg_right hTLt (by positivity)
      _ ≤ Lt / Ls := div_le_div_of_nonneg_left hLt0 hLs hLsW
  have h2 : 1 - c / W ≤ 1 - c / Ls := by
    have hcLs : c / Ls ≤ c / W := div_le_div_of_nonneg_left hc0 hW hWLs
    linarith
  have hcW' : 0 ≤ c / W := div_nonneg hc0 hW.le
  have h3 : 1 - K / W ≤ (1 - ε) * (1 - c / W) := by
    have hK : (c + ε * W) / W ≤ K / W := div_le_div_of_nonneg_right hKW hW.le
    have hexp : (c + ε * W) / W = c / W + ε := by field_simp
    have hexp2 : (1 - ε) * (1 - c / W) = 1 - c / W - ε + ε * (c / W) := by ring
    rw [hexp2]
    nlinarith [mul_nonneg hε hcW']
  have hb : 0 ≤ 1 - c / W := by
    have h : c / W ≤ 1 := by rw [div_le_one hW]; exact hcW
    linarith
  have hLtLs : 0 ≤ Lt / Ls := div_nonneg hLt0 hLs.le
  calc T / W * (1 - K / W)
      ≤ T / W * ((1 - ε) * (1 - c / W)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (T / W * (1 - ε)) * (1 - c / W) := by ring
    _ ≤ Lt / Ls * (1 - c / Ls) := mul_le_mul h1 h2 hb hLtLs

/-- **The lower dimension bound `IsLinearLower` for the sieve problem of the residue class `q`**,
with a constant that is independent of `x`, `M`, `q`. -/
theorem exists_isLinearLower_apSieve_all :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x M q : ℕ),
      Submission.ChenPlan.IsLinearLower (apSieve x M q) (M : ℝ) K := by
  obtain ⟨c, hc0, N₀, hratio⟩ := vsieve_ratio_lower_int
  obtain ⟨Y₀, hY₀⟩ := vsieve_log_lower_sharp
  set Kb : ℝ := max (max (c + 1) 4)
    (max (Real.log ((N₀ : ℝ) + 1) + 1) (Real.log ((Y₀ : ℝ) + 1) + 1)) with hKb
  have hc1 : c + 1 ≤ Kb := by rw [hKb]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have h4 : (4 : ℝ) ≤ Kb := by rw [hKb]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hN : Real.log ((N₀ : ℝ) + 1) + 1 ≤ Kb := by
    rw [hKb]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hY : Real.log ((Y₀ : ℝ) + 1) + 1 ≤ Kb := by
    rw [hKb]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hKb0 : 0 ≤ Kb := le_trans (by linarith : (0 : ℝ) ≤ c + 1) hc1
  refine ⟨Kb, hKb0, fun x M q => ?_⟩
  intro w z' hw hwz hz'M
  simp only [apSieve_prodPrimes, apSieve_nu]
  rw [prod_odd_range_eq_vsieve M hw hwz hz'M]
  have hwpos : 0 < w := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
  by_cases hcase : Real.log w ≤ Kb
  · have h1 : 1 - Kb / Real.log w ≤ 0 := by
      have h2 : (1 : ℝ) ≤ Kb / Real.log w := by rw [one_le_div hlogw]; exact hcase
      linarith
    have h2 : (Real.log z' / Real.log w) * (1 - Kb / Real.log w) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (div_nonneg hlogz'.le hlogw.le) h1
    have h3 : (0 : ℝ) ≤ Vsieve (max ⌈w⌉₊ 3) / Vsieve ⌈z'⌉₊ :=
      div_nonneg (le_of_lt (Vsieve_pos _)) (le_of_lt (Vsieve_pos _))
    linarith
  · push_neg at hcase
    -- basic size of `w`
    have hw1 : (1 : ℝ) < w := by linarith
    have hw5 : (5 : ℝ) < w := by
      have := Real.log_le_sub_one_of_pos hwpos
      linarith
    have hs_eq : max ⌈w⌉₊ 3 = ⌈w⌉₊ := by
      apply max_eq_left
      have h : 2 < ⌈w⌉₊ := Nat.lt_ceil.mpr (lt_trans (by norm_num) hw5)
      omega
    -- the integer bounds
    have hNw : (N₀ : ℝ) + 1 < w :=
      (Real.log_lt_log_iff (by positivity) hwpos).mp (by linarith)
    have hYw : (Y₀ : ℝ) + 1 < w :=
      (Real.log_lt_log_iff (by positivity) hwpos).mp (by linarith)
    have hN_le_s : N₀ ≤ max ⌈w⌉₊ 3 := by
      have h1 : ((N₀ : ℕ) : ℝ) ≤ ((max ⌈w⌉₊ 3 : ℕ) : ℝ) := by
        have h2 : ((N₀ : ℕ) : ℝ) ≤ w := by linarith
        have h3 : w ≤ ((⌈w⌉₊ : ℕ) : ℝ) := Nat.le_ceil w
        have h4 : ((⌈w⌉₊ : ℕ) : ℝ) ≤ ((max ⌈w⌉₊ 3 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_max_left ⌈w⌉₊ 3
        linarith
      exact_mod_cast h1
    have hst : max ⌈w⌉₊ 3 ≤ ⌈z'⌉₊ := by
      refine max_le (Nat.ceil_mono (le_of_lt hwz)) ?_
      have h : 2 < ⌈z'⌉₊ := Nat.lt_ceil.mpr (lt_trans (by norm_num) (lt_trans hw5 hwz))
      omega
    have hY_t : Y₀ ≤ ⌈z'⌉₊ := by
      have h1 : ((Y₀ : ℕ) : ℝ) ≤ ((⌈z'⌉₊ : ℕ) : ℝ) := by
        have h2 : ((Y₀ : ℕ) : ℝ) ≤ w := by linarith
        have h3 : w ≤ ((⌈z'⌉₊ : ℕ) : ℝ) :=
          le_trans (Nat.le_ceil w) (by exact_mod_cast Nat.ceil_mono (le_of_lt hwz))
        linarith
      exact_mod_cast h1
    have hint := hratio (max ⌈w⌉₊ 3) ⌈z'⌉₊ hN_le_s hst
    -- the algebra
    have hLs : 0 < Real.log ((max ⌈w⌉₊ 3 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < max ⌈w⌉₊ 3))
    have hTLt : Real.log z' ≤ Real.log ((⌈z'⌉₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (Nat.le_ceil z')
    have hWLs : Real.log w ≤ Real.log ((max ⌈w⌉₊ 3 : ℕ) : ℝ) :=
      Real.log_le_log hwpos
        (le_trans (Nat.le_ceil w) (by exact_mod_cast Nat.le_max_left ⌈w⌉₊ 3))
    have hLsW : Real.log ((max ⌈w⌉₊ 3 : ℕ) : ℝ)
        ≤ Real.log w * (1 + 1 / (w * Real.log w)) := by
      rw [hs_eq]
      have hceil : ((⌈w⌉₊ : ℕ) : ℝ) < w + 1 := Nat.ceil_lt_add_one (by linarith)
      have h1 : Real.log ((⌈w⌉₊ : ℕ) : ℝ) ≤ Real.log (w + 1) :=
        Real.log_le_log (by positivity) (le_of_lt hceil)
      have h2 : Real.log (w + 1) = Real.log w + Real.log (1 + 1 / w) := by
        rw [show w + 1 = w * (1 + 1 / w) by field_simp]
        rw [Real.log_mul (by linarith) (by positivity)]
      have h3 : Real.log (1 + 1 / w) ≤ 1 / w := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / w by positivity)
        linarith
      have h4 : Real.log w * (1 + 1 / (w * Real.log w)) = Real.log w + 1 / w := by
        field_simp
      rw [h4]
      linarith
    have hKW : c + 1 / (w * Real.log w) * Real.log w ≤ Kb := by
      have h1 : 1 / (w * Real.log w) * Real.log w = 1 / w := by field_simp
      have h2 : 1 / w ≤ 1 := by
        rw [div_le_one hwpos]; linarith
      linarith
    have hcW : c ≤ Real.log w := by linarith
    have hkey := lower_key_step (T := Real.log z') (W := Real.log w)
      (Lt := Real.log ((⌈z'⌉₊ : ℕ) : ℝ)) (Ls := Real.log ((max ⌈w⌉₊ 3 : ℕ) : ℝ))
      (K := Kb) (c := c) (ε := 1 / (w * Real.log w))
      hlogz'.le hlogw hLs hTLt hWLs hLsW (by positivity) hc0 hcW hKW
    exact hkey.trans hint

/-- **The upper linear sieve at the residue class `q`**, against the 2026-09-24 interface: the
`z₀ ≤ z` hypothesis is passed through and the per-`q` sieve problem must satisfy `IsLinearLower`. -/
theorem apMass_le_main_add_rem_v6 {x M q : ℕ} (hqp : q.Prime) (hqM : M ≤ q)
    {K η D₀ z₀ : ℝ} (_hη : 0 < η)
    (hU : ∀ (s : BoundingSieve) (z D : ℝ),
      D₀ ≤ D → z₀ ≤ z → 2 ≤ z → Submission.ChenPlan.IsLinear s z K →
      Submission.ChenPlan.IsLinearRange s z K → Submission.ChenPlan.IsLinearLower s z K →
      Submission.ChenPlan.IsLinearMertens s z K →
      0 ≤ s.totalMass →
      1 ≤ Real.log D / Real.log z →
      s.siftedSum ≤ s.totalMass * Submission.ChenPlan.sieveV s
        * (Submission.ChenPlan.Utab (Real.log D / Real.log z) + η)
        + Submission.ChenPlan.remSum s D)
    {Λ : ℝ} (hΛ : D₀ ≤ Λ) (hz₀ : z₀ ≤ (M : ℝ)) (hM2 : 2 ≤ (M : ℝ))
    (hlin : Submission.ChenPlan.IsLinear (apSieve x M q) (M : ℝ) K)
    (hlinr : Submission.ChenPlan.IsLinearRange (apSieve x M q) (M : ℝ) K)
    (hlinl : Submission.ChenPlan.IsLinearLower (apSieve x M q) (M : ℝ) K)
    (hlinm : Submission.ChenPlan.IsLinearMertens (apSieve x M q) (M : ℝ) K)
    (hlog : 1 ≤ Real.log Λ / Real.log (M : ℝ)) :
    Submission.apMass x M q
      ≤ (x : ℝ) / (q.totient : ℝ) * VsieveOdd M
          * (Submission.ChenPlan.Utab (Real.log Λ / Real.log (M : ℝ)) + η)
        + remSumQ x M q Λ := by
  have htot : 0 ≤ (apSieve x M q).totalMass := by
    rw [apSieve_totalMass]
    positivity
  have h := hU (apSieve x M q) (M : ℝ) Λ hΛ hz₀ hM2 hlin hlinr hlinl hlinm htot hlog
  rw [apSieve_siftedSum, apSieve_totalMass, apSieve_sieveV, apSieve_remSum hqp hqM Λ] at h
  exact h
/-! ## The assembly (copied from `Assembly.lean`, with the range hypothesis passed through) -/
/-- `VsieveOdd M > 0`. -/
lemma VsieveOdd_pos_range (M : ℕ) : 0 < VsieveOdd M := by
  unfold VsieveOdd
  refine Finset.prod_pos (fun p hp => ?_)
  obtain ⟨hpp, hp3, _⟩ := Submission.mem_oddLt.mp hp
  have h1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hpp.one_lt
  have h2 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have h3 : (1:ℝ) / ((p:ℝ) - 1) < 1 := by
    rw [div_lt_one h2]
    have h4 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
    linarith
  linarith

/-- The sum of the prime reciprocals over the window is eventually at most seven. -/
lemma eventually_window_recip_le_range :
    ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ Submission.winPrimes (siftM x) (winY x), 1 / ((q : ℝ) - 1)) ≤ 10 := by
  obtain ⟨C, hCpos, X₀, hX₀⟩ := Work.Sieve.RosserLinear.primeRecipsLocalUpper 1 (by norm_num)
  filter_upwards [eventually_siftM_ge (max X₀ 100),
    eventually_siftM_le_winY,
    eventually_wVal_le (δ := (1:ℝ)/100) (by norm_num),
    eventually_log_siftM_ge (c := max 4 (2 * C + 1))
      (le_trans (by norm_num : (1:ℝ) ≤ 4) (le_max_left _ _))] with x hM hMY hw hl
  have hX0x : X₀ ≤ siftM x := le_trans (le_max_left _ _) hM
  have h100 : 100 ≤ siftM x := le_trans (le_max_right _ _) hM
  have hlogM1 : (1 : ℝ) ≤ Real.log (siftM x : ℝ) :=
    le_trans (show (1:ℝ) ≤ max 4 (2 * C + 1) from
      le_trans (by norm_num) (le_max_left (4:ℝ) (2 * C + 1))) hl
  have hlogMpos : 0 < Real.log (siftM x : ℝ) := lt_of_lt_of_le one_pos hlogM1
  have hlogMbig : 2 * C + 1 ≤ Real.log (siftM x : ℝ) := le_trans (le_max_right _ _) hl
  have hMpos : 0 < (siftM x : ℝ) := by
    have : 0 < siftM x := by omega
    exact_mod_cast this
  have hYpos : 0 < (winY x : ℝ) := by
    have : 0 < winY x := by omega
    exact_mod_cast this
  have hsub : Submission.winPrimes (siftM x) (winY x) ⊆
      (Finset.Icc (siftM x) (winY x - 1)).filter Nat.Prime := by
    intro q hq
    obtain ⟨hqp, hq3, hqM, hqY⟩ := Submission.mem_winPrimes.mp hq
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hqM, by omega⟩, hqp⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => ?_)) ?_
  · have hq' : Nat.Prime q := (Finset.mem_filter.mp hq).2
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq'.one_le
    exact div_nonneg (by norm_num) (by linarith)
  refine le_trans (hX₀ (siftM x) (winY x) hX0x (by omega)) ?_
  -- `log Y / log M ≤ 7/2`
  have hw' : Real.log (((winY x - 1 : ℕ)) : ℝ) / Real.log (siftM x : ℝ) ≤ 10 / 3 + 1 / 100 := hw
  have hlogY1 : Real.log (((winY x - 1 : ℕ)) : ℝ) ≤ (10 / 3 + 1 / 100) * Real.log (siftM x : ℝ) := by
    rw [div_le_iff₀ hlogMpos] at hw'
    exact hw'
  have hYle2 : (winY x : ℝ) ≤ 2 * (((winY x - 1 : ℕ)) : ℝ) := by
    have h3 : (((winY x - 1 : ℕ)) : ℝ) = ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) + 1 := by
      rw [winY_sub_one_eq]; push_cast; ring
    rw [h3, winY_eq]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊]
  have hpos_sub : 0 < (((winY x - 1 : ℕ)) : ℝ) := by
    have : 0 < winY x - 1 := by omega
    exact_mod_cast this
  have hlogY2 : Real.log (winY x : ℝ) ≤ Real.log 2 + Real.log (((winY x - 1 : ℕ)) : ℝ) := by
    calc Real.log (winY x : ℝ) ≤ Real.log (2 * (((winY x - 1 : ℕ)) : ℝ)) :=
          Real.log_le_log hYpos hYle2
      _ = Real.log 2 + Real.log (((winY x - 1 : ℕ)) : ℝ) := by
          rw [Real.log_mul (by norm_num) (ne_of_gt hpos_sub)]
  have hlog2 : Real.log 2 ≤ Real.log (siftM x : ℝ) := by
    apply Real.log_le_log (by norm_num)
    have : (2 : ℕ) ≤ siftM x := by omega
    exact_mod_cast this
  have hlogY3 : Real.log (winY x : ℝ) ≤ (5 : ℝ) * Real.log (siftM x : ℝ) := by
    have h1 : (10 / 3 + 1 / 100 : ℝ) ≤ 5 - 1 := by norm_num
    nlinarith [hlogY1, hlogY2, hlog2, hlogMpos]
  have hratio : Real.log (winY x : ℝ) / Real.log (siftM x : ℝ) ≤ 5 := by
    rw [div_le_iff₀ hlogMpos]
    exact hlogY3
  have hmain : Real.log (Real.log (winY x : ℝ) / Real.log (siftM x : ℝ)) ≤ 5 := by
    have hratio1 : (1 : ℝ) ≤ Real.log (winY x : ℝ) / Real.log (siftM x : ℝ) := by
      rw [le_div_iff₀ hlogMpos, one_mul]
      refine Real.log_le_log hMpos ?_
      exact_mod_cast (by omega : siftM x ≤ winY x)
    calc Real.log (Real.log (winY x : ℝ) / Real.log (siftM x : ℝ))
        ≤ Real.log (winY x : ℝ) / Real.log (siftM x : ℝ) := by
          have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hratio1)
          linarith
      _ ≤ 5 := hratio
  -- the two error terms are at most `1`
  have hL2 : (Real.log (siftM x : ℝ)) ^ ((1 : ℝ) + 1)
      = Real.log (siftM x : ℝ) * Real.log (siftM x : ℝ) := by
    rw [show ((1 : ℝ) + 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_two]
  have herr1 : C * Real.log (Real.log (winY x : ℝ) / Real.log (siftM x : ℝ))
      / (Real.log (siftM x : ℝ)) ^ (1 : ℝ) ≤ 5 / 2 := by
    rw [Real.rpow_one, div_le_iff₀ hlogMpos]
    have h2 : C * Real.log (Real.log (winY x : ℝ) / Real.log (siftM x : ℝ)) ≤ C * 5 :=
      mul_le_mul_of_nonneg_left hmain hCpos.le
    have h4 : C * 5 ≤ Real.log (siftM x : ℝ) * (5 / 2) := by nlinarith [hlogMbig, hCpos]
    linarith
  have herr2 : C / (Real.log (siftM x : ℝ)) ^ ((1 : ℝ) + 1) ≤ 1 := by
    rw [hL2, div_le_iff₀ (by positivity)]
    have h4 : C ≤ (2 * C + 1) ^ 2 := by nlinarith [hCpos, sq_nonneg C]
    nlinarith [h4, hlogMbig, hCpos]
  linarith [hmain, herr1, herr2]

set_option maxHeartbeats 1000000 in
/-- **Chen's `h2` from the upper linear sieve.** -/
theorem h2_of_sieve_aux_three (hU : Submission.ChenPlan.LinearSieveUpper) :
    Submission.ChenPlan.H2Statement := by
  obtain ⟨K, hK, hrate⟩ := exists_mertens_ratio
  obtain ⟨Klow, _hKlow0, hLow⟩ := exists_isLinearLower_apSieve_all
  obtain ⟨KM, _hKM0, hMert⟩ := oddPrimLt_mertens_bound
  set Kbig : ℝ := max (max (rangeK K) Klow) KM with hKbigdef
  have hKbig0 : (0 : ℝ) ≤ Kbig := by
    rw [hKbigdef]
    exact le_trans (rangeK_nonneg hK) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hKbig1 : rangeK K ≤ Kbig := by
    rw [hKbigdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hKbig2 : Klow ≤ Kbig := by
    rw [hKbigdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hKbig3 : KM ≤ Kbig := by rw [hKbigdef]; exact le_max_right _ _
  have hη : (0 : ℝ) < 1 / 1000000 := by norm_num
  obtain ⟨D₀, z₀, hD₀⟩ := hU Kbig hKbig0 (1 / 1000000) hη
  obtain ⟨B, hB, hBV⟩ := weighted_rem_bound_shiftRem 3 (by norm_num)
  have hrem := remSumQ_sum_le hB (by norm_num : (0:ℝ) < 3) hBV
  have hmain := window_Ut_sum_le B hB
  have hrecip := eventually_window_recip_le_range
  have hV := Work.NumberTheory.Chen.mertens_lower_tenth
  filter_upwards [hrem, hmain, hrecip, hV, eventually_siftM_ge (max 8 ⌈max z₀ 0⌉₊),
    eventually_lvlD_div_winY_ge B hB D₀, eventually_siftM_mul_winY_le_lvlD B hB,
    eventually_siftM_le_winY, eventually_ge_atTop 8, eventually_log_ge 100]
    with x hremx hmainx hrecipx hVx hMbig hlvl hMYle hMY hx8 hlogx
  have hM8 : 8 ≤ siftM x := le_trans (le_max_left _ _) hMbig
  have hz₀M : z₀ ≤ (siftM x : ℝ) := by
    have h1 : z₀ ≤ ((⌈max z₀ 0⌉₊ : ℕ) : ℝ) :=
      le_trans (le_max_left z₀ 0) (Nat.le_ceil (max z₀ 0))
    have h2 : ((⌈max z₀ 0⌉₊ : ℕ) : ℝ) ≤ (siftM x : ℝ) := by
      exact_mod_cast (le_trans (le_max_right _ _) hMbig)
    linarith
  -- notation
  set M : ℕ := siftM x with hMdef
  set Y : ℕ := winY x with hYdef
  set V : ℝ := VsieveOdd M with hVdef
  set η : ℝ := 1 / 1000000 with hηdef
  have hM4 : 4 ≤ M := by rw [hMdef]; omega
  have hVpos : 0 < V := by rw [hVdef]; exact VsieveOdd_pos_range M
  have hMYlvl : (M : ℝ) * (Y : ℝ) ≤ lvlD B x := by rw [hMdef, hYdef]; exact hMYle
  -- the per-`q` sieve bound
  have hper : ∀ q ∈ Submission.winPrimes M Y,
      Submission.apMass x M q
        ≤ (x : ℝ) / (q.totient : ℝ) * V * (Submission.ChenPlan.Utab (sVal B x q) + η)
          + remSumQ x M q (lvlD B x / (q : ℝ)) := by
    intro q hq
    obtain ⟨hqp, hq3, hqM, hqY⟩ := Submission.mem_winPrimes.mp hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqp.pos
    have hqle : (q : ℝ) ≤ (Y : ℝ) := by
      rw [hYdef]; exact_mod_cast (by omega : q ≤ winY x)
    have hlvlq : D₀ ≤ lvlD B x / (q : ℝ) := by
      have hlvlD0 : 0 ≤ lvlD B x := by rw [lvlD]; positivity
      have h1 : lvlD B x / (Y : ℝ) ≤ lvlD B x / (q : ℝ) :=
        div_le_div_of_nonneg_left hlvlD0 hqpos hqle
      exact le_trans hlvl h1
    have hM2 : (2 : ℝ) ≤ (M : ℝ) := by rw [hMdef]; exact_mod_cast (by omega : 2 ≤ siftM x)
    have hK' : 0 ≤ rangeK K := rangeK_nonneg hK
    have hrate' : ∀ (z : ℕ) (wt : ℝ), 2 ≤ wt → wt < z →
        (∏ p ∈ (Finset.range z).filter (fun p : ℕ => p.Prime ∧ wt ≤ (p : ℝ)),
            (((p : ℝ) - 1) / ((p : ℝ) - 2)))
          ≤ (Real.log (z : ℝ) / Real.log wt) * (1 + rangeK K / Real.log wt) :=
      hrate_mono (le_rangeK hK) hrate
    have hlin₀ : Submission.ChenPlan.IsLinear (apSieve x M q) (M : ℝ) (rangeK K) :=
      isLinear_apSieve x M q (by omega) hK' hrate'
    have hlin : Submission.ChenPlan.IsLinear (apSieve x M q) (M : ℝ) Kbig :=
      IsLinear_mono hlin₀ hKbig1
    have hlinr₀ : Submission.ChenPlan.IsLinearRange (apSieve x M q) (M : ℝ) (rangeK K) :=
      isLinearRange_apSieve x M q hK hrate
    have hlinr : Submission.ChenPlan.IsLinearRange (apSieve x M q) (M : ℝ) Kbig :=
      IsLinearRange_mono hlinr₀ hKbig1
    have hlinl : Submission.ChenPlan.IsLinearLower (apSieve x M q) (M : ℝ) Kbig :=
      IsLinearLower_mono (hLow x M q) hKbig2
    have hlinm : Submission.ChenPlan.IsLinearMertens (apSieve x M q) (M : ℝ) Kbig :=
      IsLinearMertens_mono (isLinearMertens_apSieve x M q hMert) hKbig3
    have hlog : 1 ≤ sVal B x q := by
      rw [hMdef, hYdef] at hMYlvl
      exact one_le_sVal hqM (by rw [← hYdef]; exact hqY) (by omega) hMYle (by omega)
    have hz₀M' : z₀ ≤ (M : ℝ) := by rw [hMdef]; exact hz₀M
    have := apMass_le_main_add_rem_v6 hqp hqM hη hD₀ hlvlq hz₀M' hM2 hlin hlinr hlinl hlinm hlog
    rw [hVdef]
    exact this
  -- sum the bounds
  have hsum := Finset.sum_le_sum hper
  have hrearr : (∑ q ∈ Submission.winPrimes M Y,
        ((x : ℝ) / (q.totient : ℝ) * V * (Submission.ChenPlan.Utab (sVal B x q) + η)
          + remSumQ x M q (lvlD B x / (q : ℝ))))
      = V * (x : ℝ) * (∑ q ∈ Submission.winPrimes M Y,
            (Submission.ChenPlan.Utab (sVal B x q) + η) / ((q : ℝ) - 1))
        + ∑ q ∈ Submission.winPrimes M Y, remSumQ x M q (lvlD B x / (q : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    have hqq : (∑ i ∈ Submission.winPrimes M Y, remSumQ x M i (lvlD B x / (i : ℝ)))
        = ∑ q ∈ Submission.winPrimes M Y, remSumQ x M q (lvlD B x / (q : ℝ)) := rfl
    rw [hqq]
    congr 1
    refine Finset.sum_congr rfl (fun q hq => ?_)
    obtain ⟨hqp, hq3, hqM, hqY⟩ := Submission.mem_winPrimes.mp hq
    have h1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      push_cast [Nat.cast_sub hqp.one_le]; ring
    rw [Nat.totient_prime hqp, h1]
    ring
  have hsplit : (∑ q ∈ Submission.winPrimes M Y,
            (Submission.ChenPlan.Utab (sVal B x q) + η) / ((q : ℝ) - 1))
      = (∑ q ∈ Submission.winPrimes M Y, Submission.ChenPlan.Utab (sVal B x q) / ((q : ℝ) - 1))
        + η * (∑ q ∈ Submission.winPrimes M Y, 1 / ((q : ℝ) - 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    ring
  -- final bookkeeping
  have hmainx' : (∑ q ∈ Submission.winPrimes M Y,
      Submission.ChenPlan.Utab (sVal B x q) / ((q : ℝ) - 1)) ≤ 39 / 25 - 1 / 1000 := by
    rw [hMdef, hYdef]; exact hmainx
  have hrecipx' : (∑ q ∈ Submission.winPrimes M Y, 1 / ((q : ℝ) - 1)) ≤ 10 := by
    rw [hMdef, hYdef]; exact hrecipx
  have hremx' : (∑ q ∈ Submission.winPrimes M Y, remSumQ x M q (lvlD B x / (q : ℝ)))
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 3 := by
    simpa [hMdef, hYdef, Real.rpow_natCast] using hremx
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 0 ≤ x)
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hηpos : 0 < η := by rw [hηdef]; norm_num
  have hV6 : (34 / 5 : ℝ) ≤ V * Real.log (x : ℝ) := by
    have h1 : (34 / 5 : ℝ) * (x : ℝ) ≤ (x : ℝ) * V * Real.log (x : ℝ) := by
      rw [hVdef, hMdef]; exact hVx
    have h2 : (34 / 5 : ℝ) / Real.log (x : ℝ) ≤ V := by
      rw [div_le_iff₀ hlogpos]
      nlinarith [h1, hxpos]
    rwa [div_le_iff₀ hlogpos] at h2
  have habsorb : (x : ℝ) / (Real.log (x : ℝ)) ^ 3 ≤ V * (x : ℝ) * (1 / 1000 - 10 * η) := by
    have hηsmall : (1 : ℝ) / 2000 ≤ 1 / 1000 - 10 * η := by
      rw [hηdef]; norm_num
    have hlog2 : (10000 : ℝ) ≤ Real.log (x : ℝ) * Real.log (x : ℝ) := by nlinarith [hlogx]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Real.log (x : ℝ)) ^ 3)]
    have h3 : (Real.log (x : ℝ)) ^ 3
        = Real.log (x : ℝ) * Real.log (x : ℝ) * Real.log (x : ℝ) := by ring
    rw [h3]
    have hL2 : (0:ℝ) ≤ Real.log (x:ℝ) * Real.log (x:ℝ) := mul_nonneg hlogpos.le hlogpos.le
    have hA : (34/5 : ℝ) * (1/2000) ≤ (V * Real.log (x:ℝ)) * (1/1000 - 10*η) :=
      mul_le_mul hV6 hηsmall (by norm_num) (by positivity)
    have hB : (34/5 : ℝ) * (1/2000) * (10000:ℝ)
        ≤ (V * Real.log (x:ℝ)) * (1/1000 - 10*η) * (Real.log (x:ℝ) * Real.log (x:ℝ)) :=
      mul_le_mul hA hlog2 (by norm_num) (by positivity)
    nlinarith [hB, hx0, hlogpos]
  have hfinal : V * (x : ℝ) * ((39 / 25 - 1 / 1000) + η * 10)
      + (x : ℝ) / (Real.log (x : ℝ)) ^ 3 ≤ 39 / 25 * ((x : ℝ) * V) := by
    have h1 : V * (x : ℝ) * ((39 / 25 - 1 / 1000) + η * 10)
        = V * (x : ℝ) * (39 / 25) - V * (x : ℝ) * (1 / 1000 - 10 * η) := by ring
    rw [h1]
    nlinarith [habsorb]
  have hstep1 : V * (x : ℝ) * ((∑ q ∈ Submission.winPrimes M Y,
        Submission.ChenPlan.Utab (sVal B x q) / ((q : ℝ) - 1))
      + η * (∑ q ∈ Submission.winPrimes M Y, 1 / ((q : ℝ) - 1)))
      + (∑ q ∈ Submission.winPrimes M Y, remSumQ x M q (lvlD B x / (q : ℝ)))
      ≤ V * (x : ℝ) * ((39 / 25 - 1 / 1000) + η * 10)
        + (x : ℝ) / (Real.log (x : ℝ)) ^ 3 := by
    have hb1 : (∑ q ∈ Submission.winPrimes M Y,
          Submission.ChenPlan.Utab (sVal B x q) / ((q : ℝ) - 1))
        + η * (∑ q ∈ Submission.winPrimes M Y, 1 / ((q : ℝ) - 1))
        ≤ (39 / 25 - 1 / 1000) + η * 10 := by
      nlinarith [hmainx', hrecipx', hηpos]
    have hb2 := mul_le_mul_of_nonneg_left hb1 (by positivity : (0:ℝ) ≤ V * (x:ℝ))
    exact add_le_add hb2 hremx'
  calc (∑ q ∈ Submission.winPrimes M Y, Submission.apMass x M q)
      ≤ ∑ q ∈ Submission.winPrimes M Y,
          ((x : ℝ) / (q.totient : ℝ) * V * (Submission.ChenPlan.Utab (sVal B x q) + η)
            + remSumQ x M q (lvlD B x / (q : ℝ))) := hsum
    _ = V * (x : ℝ) * (∑ q ∈ Submission.winPrimes M Y,
            (Submission.ChenPlan.Utab (sVal B x q) + η) / ((q : ℝ) - 1))
        + ∑ q ∈ Submission.winPrimes M Y, remSumQ x M q (lvlD B x / (q : ℝ)) := hrearr
    _ = V * (x : ℝ) * ((∑ q ∈ Submission.winPrimes M Y,
            Submission.ChenPlan.Utab (sVal B x q) / ((q : ℝ) - 1))
          + η * (∑ q ∈ Submission.winPrimes M Y, 1 / ((q : ℝ) - 1)))
        + ∑ q ∈ Submission.winPrimes M Y, remSumQ x M q (lvlD B x / (q : ℝ)) := by
        rw [hsplit]
    _ ≤ V * (x : ℝ) * ((39 / 25 - 1 / 1000) + η * 10)
        + (x : ℝ) / (Real.log (x : ℝ)) ^ 3 := hstep1
    _ ≤ 39 / 25 * ((x : ℝ) * V) := hfinal
    _ = 39 / 25 * (x : ℝ) * VsieveOdd (Submission.chenSiftLimitTenth x) := by
        rw [hVdef, hMdef, siftM]
        ring

/-- **Chen's h2 from the linear sieve, against the v6 interface (`IsLinearMertens`).** -/
theorem h2_of_sieve_three (hU : Submission.ChenPlan.LinearSieveUpper) :
    Submission.ChenPlan.H2Statement :=
  h2_of_sieve_aux_three hU

end

end Work.ChenPlan.H2
