import Mathlib
import Submission.Work.LinnikAreas.CIDeps
import Submission.Commons.NumberTheory.Linnik.tentWeight_bounds
import Submission.Commons.NumberTheory.Primes.prime_dvd_of_prime_pow_not_coprime

/-!
# Uniform tail bound for the non-coprime part of the tent-weighted von Mangoldt sum

For `q ≥ 2`, `X : ℕ` and the tent weight `f = tentWeight L K` (supported on `[L - 2K, L]`,
with `0 ≤ f ≤ K`), the contribution of the integers `n ≤ X` that are **not** coprime to `q`
to the tent-weighted von Mangoldt sum satisfies

`Σ_{n ≤ X, (n,q) > 1} Λ(n)/n · f(log n / log q) ≤ C · (log q)² · q^{-(L-2K)}`

with a constant `C = 4K` that is *absolute*: independent of `q`, of `X` and of the arithmetic
progression.  This is the uniform version of
`Commons.NumberTheory.Linnik.tentSum_nonCoprime_bound`, whose constant `2K · ω(q)` depends on
`q`; here the number of distinct prime factors of `q` is replaced by `log q / log 2 ≤ 2 log q`.
-/

open scoped BigOperators

namespace Work.LinnikAreas

attribute [local instance] Classical.propDecidable

/-- The number of distinct prime factors of `q` is at most `log q / log 2`. -/
lemma card_primeFactors_le_log_div_log_two {q : ℕ} (hq : 2 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
  have hnat : 2 ^ q.primeFactors.card ≤ q := by
    have hprod : (∏ _p ∈ q.primeFactors, (2 : ℕ)) ≤ ∏ p ∈ q.primeFactors, p := by
      apply Finset.prod_le_prod₀
      · intro p _
        norm_num
      · intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).two_le
    rw [Finset.prod_const] at hprod
    exact le_trans hprod (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q))
  have hreal : (2 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) := by exact_mod_cast hnat
  have hlog : Real.log ((2 : ℝ) ^ q.primeFactors.card) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by positivity) hreal
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  exact hlog

/-- Below the threshold `q^(L-2K)` the tent weight vanishes. -/
private lemma tentWeight_vanish_below' {L K : ℝ} (hK : 0 ≤ K) (h2K : 2 * K ≤ L) {q n : ℕ}
    (hq : 2 ≤ q) (hn : 1 ≤ n) (hnT : (n : ℝ) ≤ (q : ℝ) ^ (L - 2 * K)) :
    Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) = 0 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlog_le : Real.log (n : ℝ) ≤ Real.log ((q : ℝ) ^ (L - 2 * K)) :=
    Real.log_le_log hnR hnT
  rw [Real.log_rpow hqR] at hlog_le
  have hdiv : Real.log (n : ℝ) / Real.log (q : ℝ) ≤ L - 2 * K := by
    rw [div_le_iff₀ hlogq]
    exact hlog_le
  exact (Commons.NumberTheory.Linnik.tentWeight_bounds hK h2K).2.2.1 _ hdiv

/-- The double sum over pairs `(p,k)` with `p` a prime factor of `q` is nonnegative. -/
private lemma primeFactor_doubleSum_nonneg' (q X n : ℕ) (hn : 1 ≤ n) :
    0 ≤ ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X,
          (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else 0) := by
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro k _
  by_cases hk' : n = p ^ k
  · rw [if_pos hk']
    exact div_nonneg (Real.log_nonneg (by
      have := Nat.prime_of_mem_primeFactors hp
      exact_mod_cast this.one_le)) (by positivity)
  · rw [if_neg hk']

/-- Pointwise bound for a single summand: for `n ≤ X` not coprime to `q`, the summand is
bounded by `K` times the double sum over prime-factor/exponent pairs. -/
private lemma term_le_doubleSum' {q X : ℕ} (hq : 2 ≤ q) {L K : ℝ} (hK : 0 ≤ K)
    (h2K : 2 * K ≤ L) {n : ℕ} (hn1 : 1 ≤ n) (hnX : n ≤ X) (hcop : ¬ Nat.Coprime n q) :
    ArithmeticFunction.vonMangoldt n / (n : ℝ) *
        Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))
      ≤ K * ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X,
          (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else 0) := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨p0, k0, hp0, hk0, hnk⟩ := (isPrimePow_nat_iff n).mp hpp
    have hmemP : p0 ∈ q.primeFactors :=
      Nat.Prime.mem_primeFactors hp0
        (Commons.NumberTheory.Primes.prime_dvd_of_prime_pow_not_coprime hp0 hk0 hnk hcop)
        (by omega)
    have hk0X : k0 ≤ X := by
      have hp2 : 2 ≤ p0 := hp0.two_le
      have h2k : 2 ^ k0 ≤ X := by
        calc 2 ^ k0 ≤ p0 ^ k0 := Nat.pow_le_pow_left hp2 k0
          _ = n := hnk
          _ ≤ X := hnX
      exact le_trans (le_of_lt Nat.lt_two_pow_self) h2k
    have hmemk : k0 ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨hk0, hk0X⟩
    have hLam : ArithmeticFunction.vonMangoldt n = Real.log (p0 : ℝ) := by
      rw [← hnk, ArithmeticFunction.vonMangoldt_apply_pow hk0.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hp0]
    have hlogp0 : 0 ≤ Real.log (p0 : ℝ) := Real.log_nonneg (by exact_mod_cast hp0.one_le)
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hinner_term : (if n = p0 ^ k0 then Real.log (p0 : ℝ) / (n : ℝ) else 0)
        = Real.log (p0 : ℝ) / (n : ℝ) := by rw [if_pos hnk.symm]
    have h_inner : Real.log (p0 : ℝ) / (n : ℝ)
        ≤ ∑ k ∈ Finset.Icc 1 X, (if n = p0 ^ k then Real.log (p0 : ℝ) / (n : ℝ) else 0) := by
      have h := Finset.single_le_sum
        (s := Finset.Icc 1 X)
        (f := fun k : ℕ => (if n = p0 ^ k then Real.log (p0 : ℝ) / (n : ℝ) else (0 : ℝ)))
        (fun k _ => by
          by_cases hk : n = p0 ^ k
          · rw [if_pos hk]; exact div_nonneg hlogp0 (le_of_lt hnpos)
          · rw [if_neg hk]) hmemk
      rwa [hinner_term] at h
    have h_outer : (∑ k ∈ Finset.Icc 1 X,
          (if n = p0 ^ k then Real.log (p0 : ℝ) / (n : ℝ) else 0))
        ≤ ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X,
            (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else 0) := by
      refine Finset.single_le_sum
        (f := fun p : ℕ => ∑ k ∈ Finset.Icc 1 X,
            (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else (0 : ℝ))) (fun p hp => ?_) hmemP
      exact Finset.sum_nonneg (fun k _ => by
        by_cases hk : n = p ^ k
        · rw [if_pos hk]; exact div_nonneg (Real.log_nonneg (by
            have := Nat.prime_of_mem_primeFactors hp
            exact_mod_cast this.one_le)) (le_of_lt hnpos)
        · rw [if_neg hk])
    have hf : Commons.NumberTheory.Linnik.tentWeight L K
        (Real.log (n : ℝ) / Real.log (q : ℝ)) ≤ K :=
      (Commons.NumberTheory.Linnik.tentWeight_bounds hK h2K).2.1 _
    calc ArithmeticFunction.vonMangoldt n / (n : ℝ) *
            Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))
          = (Real.log (p0 : ℝ) / (n : ℝ)) *
            Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) := by
            rw [hLam]
        _ ≤ (Real.log (p0 : ℝ) / (n : ℝ)) * K := by
            exact mul_le_mul_of_nonneg_left hf (div_nonneg hlogp0 (le_of_lt hnpos))
        _ = K * (Real.log (p0 : ℝ) / (n : ℝ)) := by ring
        _ ≤ K * (∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X,
              (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else 0)) := by
            exact mul_le_mul_of_nonneg_left (le_trans h_inner h_outer) hK
  · have hLam0 : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    rw [hLam0, zero_div, zero_mul]
    exact mul_nonneg hK (primeFactor_doubleSum_nonneg' q X n hn1)

/-- Geometric tail bound: summing `(p⁻¹)^k` over the exponents `k ≤ X` with `T < p^k`
is at most `2/T`. -/
private lemma sum_Icc_filter_inv_pow_le' {p T : ℝ} {X : ℕ} (hp : 2 ≤ p) (hT : 0 < T) :
    (∑ k ∈ (Finset.Icc 1 X).filter (fun k => T < p ^ k), (p⁻¹) ^ k) ≤ 2 / T := by
  have hp1 : 1 < p := by linarith
  have hx0 : 0 ≤ p⁻¹ := by positivity
  have hx1 : p⁻¹ < 1 := by
    rw [inv_lt_one₀ (by linarith : (0:ℝ) < p)]; linarith
  rcases Finset.eq_empty_or_nonempty ((Finset.Icc 1 X).filter (fun k => T < p ^ k)) with hAe | hAne
  · rw [hAe, Finset.sum_empty]; positivity
  · set A := (Finset.Icc 1 X).filter (fun k => T < p ^ k) with hA
    set k0 := A.min' hAne with hk0
    have hk0A : k0 ∈ A := A.min'_mem hAne
    have hle : ∀ k ∈ A, k0 ≤ k := fun k hk => A.min'_le k hk
    have hsub : A ⊆ Finset.Icc k0 X := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨hle k hk, (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2⟩
    have hsum_le : ∑ k ∈ A, (p⁻¹)^k ≤ ∑ k ∈ Finset.Icc k0 X, (p⁻¹)^k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    have hIco : Finset.Icc k0 X = Finset.Ico k0 (X+1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIco] at hsum_le
    have hgeom := geom_sum_Ico_le_of_lt_one (x := p⁻¹) hx0 hx1 (m := k0) (n := X+1)
    have hTlt : T < p ^ k0 := (Finset.mem_filter.mp hk0A).2
    have hpk0pos : 0 < p ^ k0 := by positivity
    have hinv : (p⁻¹)^k0 < 1 / T := by
      rw [inv_pow, one_div]
      exact (inv_lt_inv₀ hpk0pos hT).mpr hTlt
    have hle2 : (1 : ℝ) - p⁻¹ ≥ 1/2 := by
      have hpinv : p⁻¹ ≤ (1:ℝ)/2 := by
        have := (inv_le_inv₀ (by linarith : (0:ℝ) < p) (by norm_num : (0:ℝ) < 2)).mpr
          (by linarith : (2:ℝ) ≤ p)
        simpa using this
      linarith
    have hdiv2 : (p⁻¹)^k0 / (1 - p⁻¹) ≤ 2 / T := by
      have h1 : (p⁻¹)^k0 / (1 - p⁻¹) ≤ (1/T) / (1/2) :=
        div_le_div₀ (by positivity) (le_of_lt hinv) (by norm_num) hle2
      have h2 : (1/T) / (1/2) = 2/T := by ring
      rw [h2] at h1; exact h1
    exact le_trans (le_trans hsum_le hgeom) hdiv2

/-- **Uniform non-coprime tail bound.**  For any `L, K` with `0 < K` and `2K < L` there is an
absolute constant `C = 4K` such that for every `q ≥ 2` and every `X` the non-coprime part of the
tent-weighted von Mangoldt sum is at most `C (log q)² q^{-(L-2K)}`. -/
theorem tentSum_nonCoprime_uniform {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ X : ℕ,
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q),
          ArithmeticFunction.vonMangoldt n / (n : ℝ) *
            Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)))
        ≤ C * (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-(L - 2 * K)) := by
  refine ⟨4 * K, by linarith, ?_⟩
  intro q hq X
  have hq1 : 1 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hK0 : 0 ≤ K := le_of_lt hK
  have h2Kle : 2 * K ≤ L := le_of_lt h2K
  set T : ℝ := (q : ℝ) ^ (L - 2 * K) with hTdef
  have hTpos : 0 < T := Real.rpow_pos_of_pos hqR _
  set A : Finset ℕ :=
    ((Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q)).filter
      (fun n : ℕ => T < (n : ℝ)) with hA
  have h_eq : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n / (n : ℝ) *
          Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)))
      = ∑ n ∈ A, ArithmeticFunction.vonMangoldt n / (n : ℝ) *
          Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) := by
    rw [hA]
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hTn : T < (n : ℝ)
    · rw [if_pos hTn]
    · rw [if_neg hTn]
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      have hfn : Commons.NumberTheory.Linnik.tentWeight L K
          (Real.log (n : ℝ) / Real.log (q : ℝ)) = 0 :=
        tentWeight_vanish_below' hK0 h2Kle hq hn1 (hTdef ▸ (le_of_not_gt hTn))
      rw [hfn, mul_zero]
  have h_bd1 : (∑ n ∈ A, ArithmeticFunction.vonMangoldt n / (n : ℝ) *
          Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)))
      ≤ ∑ n ∈ A, K * ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X,
          (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro n hn
    rw [hA] at hn
    have hAn : n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q) :=
      (Finset.mem_filter.mp hn).1
    have hIcc : n ∈ Finset.Icc 1 X := (Finset.mem_filter.mp hAn).1
    exact term_le_doubleSum' hq hK0 h2Kle (Finset.mem_Icc.mp hIcc).1
      (Finset.mem_Icc.mp hIcc).2 (Finset.mem_filter.mp hAn).2
  have h_reindex : (∑ n ∈ A, ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X,
          (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else 0))
      = ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X, ∑ n ∈ A,
          (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
  have h_bd3 : (∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X, ∑ n ∈ A,
          (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else 0))
      ≤ ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X,
          (if T < (p : ℝ) ^ k then Real.log (p : ℝ) / (p : ℝ) ^ k else 0) := by
    apply Finset.sum_le_sum; intro p _
    apply Finset.sum_le_sum; intro k _
    rw [Finset.sum_ite_eq']
    by_cases hmem : p ^ k ∈ A
    · rw [if_pos hmem]
      have hmem' := hmem
      rw [hA] at hmem'
      have hTk : T < ((p ^ k : ℕ) : ℝ) := (Finset.mem_filter.mp hmem').2
      have hTk' : T < (p : ℝ) ^ k := by simpa using hTk
      rw [if_pos hTk']
      simp
    · rw [if_neg hmem]
      by_cases hTk : T < (p : ℝ) ^ k
      · rw [if_pos hTk]; positivity
      · rw [if_neg hTk]
  have h_bd4 : (∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X,
          (if T < (p : ℝ) ^ k then Real.log (p : ℝ) / (p : ℝ) ^ k else 0))
      = ∑ p ∈ q.primeFactors, ∑ k ∈ (Finset.Icc 1 X).filter (fun k => T < (p:ℝ)^k),
          Real.log (p : ℝ) / (p : ℝ) ^ k := by
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.sum_filter]
  have h_bd5 : (∑ p ∈ q.primeFactors, ∑ k ∈ (Finset.Icc 1 X).filter (fun k => T < (p:ℝ)^k),
          Real.log (p : ℝ) / (p : ℝ) ^ k)
      ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) * (2 / T) := by
    apply Finset.sum_le_sum; intro p hp
    have hp2 : 2 ≤ (p:ℝ) := by
      have := Nat.prime_of_mem_primeFactors hp; exact_mod_cast this.two_le
    have hlogp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by linarith)
    have hgeo := sum_Icc_filter_inv_pow_le' (p := (p:ℝ)) (T := T) (X := X) hp2 hTpos
    calc (∑ k ∈ (Finset.Icc 1 X).filter (fun k => T < (p:ℝ)^k), Real.log (p:ℝ)/(p:ℝ)^k)
        = Real.log (p:ℝ) * ∑ k ∈ (Finset.Icc 1 X).filter (fun k => T < (p:ℝ)^k),
            ((p:ℝ)⁻¹)^k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _
          rw [div_eq_mul_inv, inv_pow]
      _ ≤ Real.log (p:ℝ) * (2 / T) := mul_le_mul_of_nonneg_left hgeo hlogp
  have h_bd6 : (∑ p ∈ q.primeFactors, Real.log (p : ℝ) * (2 / T))
      = (2 / T) * ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _; ring
  have h_bd7 : (∑ p ∈ q.primeFactors, Real.log (p : ℝ))
      ≤ (q.primeFactors.card : ℝ) * Real.log (q : ℝ) := by
    calc (∑ p ∈ q.primeFactors, Real.log (p : ℝ))
        ≤ ∑ _p ∈ q.primeFactors, Real.log (q : ℝ) := by
          apply Finset.sum_le_sum; intro p hp
          exact Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
            (by exact_mod_cast Nat.le_of_mem_primeFactors hp)
      _ = (q.primeFactors.card : ℝ) * Real.log (q : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- the uniform constant step: `ω(q) ≤ log q / log 2 ≤ 2 log q`
  have hcard2 : (q.primeFactors.card : ℝ) ≤ 2 * Real.log (q : ℝ) := by
    have hstep : Real.log (q : ℝ) / Real.log 2 ≤ 2 * Real.log (q : ℝ) := by
      rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith [hlogq.le]
    exact le_trans (card_primeFactors_le_log_div_log_two hq) hstep
  have hkey : 2 * K * (q.primeFactors.card : ℝ) * Real.log (q : ℝ)
      ≤ (4 * K) * (Real.log (q : ℝ)) ^ 2 := by
    have h1 : 2 * K * (q.primeFactors.card : ℝ) ≤ 2 * K * (2 * Real.log (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hcard2 (by positivity)
    calc 2 * K * (q.primeFactors.card : ℝ) * Real.log (q : ℝ)
        ≤ (2 * K * (2 * Real.log (q : ℝ))) * Real.log (q : ℝ) :=
          mul_le_mul_of_nonneg_right h1 hlogq.le
      _ = (4 * K) * (Real.log (q : ℝ)) ^ 2 := by ring
  have hpownn : 0 ≤ (q : ℝ) ^ (-(L - 2 * K)) := Real.rpow_nonneg hqR.le _
  calc (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n / (n : ℝ) *
          Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)))
      = ∑ n ∈ A, ArithmeticFunction.vonMangoldt n / (n : ℝ) *
          Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) := h_eq
    _ ≤ ∑ n ∈ A, K * ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X,
          (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else 0) := h_bd1
    _ = K * ∑ n ∈ A, ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X,
          (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else 0) := by rw [Finset.mul_sum]
    _ = K * (∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X, ∑ n ∈ A,
          (if n = p ^ k then Real.log (p : ℝ) / (n : ℝ) else 0)) := by rw [h_reindex]
    _ ≤ K * (∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 X,
          (if T < (p : ℝ) ^ k then Real.log (p : ℝ) / (p : ℝ) ^ k else 0)) :=
          mul_le_mul_of_nonneg_left h_bd3 hK0
    _ = K * (∑ p ∈ q.primeFactors, ∑ k ∈ (Finset.Icc 1 X).filter (fun k => T < (p:ℝ)^k),
          Real.log (p : ℝ) / (p : ℝ) ^ k) := by rw [h_bd4]
    _ ≤ K * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) * (2 / T)) :=
          mul_le_mul_of_nonneg_left h_bd5 hK0
    _ = K * ((2 / T) * ∑ p ∈ q.primeFactors, Real.log (p : ℝ)) := by rw [h_bd6]
    _ ≤ K * ((2 / T) * ((q.primeFactors.card : ℝ) * Real.log (q : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          exact mul_le_mul_of_nonneg_left h_bd7 (div_nonneg (by norm_num) hTpos.le)
    _ = 2 * K * (q.primeFactors.card : ℝ) * Real.log (q : ℝ) * (q : ℝ) ^ (-(L - 2 * K)) := by
          rw [hTdef, Real.rpow_neg hqR.le]
          ring
    _ ≤ (4 * K) * (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-(L - 2 * K)) :=
          mul_le_mul_of_nonneg_right hkey hpownn

theorem UniformNonCoprimeTail :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ X : ℕ,
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q),
          ArithmeticFunction.vonMangoldt n / (n : ℝ) *
            Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
              (Real.log (n : ℝ) / Real.log (q : ℝ)))
        ≤ C * (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-(49/10 : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ :=
    tentSum_nonCoprime_uniform (L := 11/2) (K := 3/10) (by norm_num) (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro q hq X
  have hexp : -((11:ℝ)/2 - 2 * ((3:ℝ)/10)) = -(49/10 : ℝ) := by norm_num
  simpa [hexp] using hC q hq X

end Work.LinnikAreas
