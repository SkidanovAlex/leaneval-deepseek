import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The number of primes in `[P/2, P]` is at most `π₀(P) = P/log P`

Elementary counting input for the node `N8`: the primes in the half-interval `[P/2, P]`
number at most `P/log P` for every real `P > 1`.

The proof splits at `P = 42`.

* For large `P` we use Chebyshev's bound in the dyadic-block form
  `∏_{N < p ≤ 2N} p ≤ (2N choose N) ≤ 4^N` (Mathlib `primorial_add_le` + `Nat.choose_le_two_pow`):
  each such prime is `> N`, so `N^(#{primes in (N,2N]}) ≤ 4^N`.  Since `P ≤ 2⌈P/2⌉₊` and
  `P ≥ 2⌈P/2⌉₊ - 2`, this gives
  `#{primes in [P/2,P]} ≤ 1 + ⌈P/2⌉₊ log 4 / log ⌈P/2⌉₊`, and the analytic inequality
  (proved below, valid for `⌈P/2⌉₊ ≥ 21`, i.e. `P > 42`)
  `1 + N log 4 / log N ≤ (2N-2)/log(2N-2) ≤ P/log P`.
* For `1 < P ≤ 42` the count is a finite check: with `n = ⌊P⌋₊`, the primes in `[P/2,P]`
  lie in `[⌈n/2⌉, n]` and `n/log n ≤ P/log P`; the finitely many cases `3 ≤ n ≤ 42` are
  verified by comparing `n^(#{primes in [n/2,n]}) ≤ (5/2)^n` (`interval_cases`, `norm_num`).
-/

namespace Work.N8

open Finset Real

/-- Chebyshev's product bound over a dyadic block: the product of the primes in
`{N+1, …, 2N}` is at most `4^N`.  Indeed that product divides `(2N choose N) ≤ 4^N`
since every prime `p ∈ (N, 2N]` divides `(2N)!` but not `(N!)^2`. -/
lemma prod_primes_Icc_succ_le (N : ℕ) :
    (∏ p ∈ (Finset.Icc (N + 1) (2 * N)).filter Nat.Prime, p) ≤ 4 ^ N := by
  have h := primorial_add_le (m := N) (n := N) le_rfl
  rw [primorial_add] at h
  have hIco : Finset.Ico (N + 1) (N + N + 1) = Finset.Icc (N + 1) (2 * N) := by
    ext p
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hIco] at h
  have hcancel : (∏ p ∈ (Finset.Icc (N + 1) (2 * N)).filter Nat.Prime, p) ≤ (N + N).choose N :=
    Nat.le_of_mul_le_mul_left h (primorial_pos N)
  calc (∏ p ∈ (Finset.Icc (N + 1) (2 * N)).filter Nat.Prime, p) ≤ (N + N).choose N := hcancel
    _ ≤ 2 ^ (N + N) := Nat.choose_le_two_pow _ _
    _ = 4 ^ N := by rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1; omega

/-- Chebyshev-type count for the dyadic block `(N, 2N]`: the number of primes in
`{N+1, …, 2N}` is at most `N · log 4 / log N` for `N ≥ 2`. -/
lemma card_primes_block_le (N : ℕ) (hN : 2 ≤ N) :
    (((Finset.Icc (N + 1) (2 * N)).filter Nat.Prime).card : ℝ) ≤
      (N : ℝ) * Real.log 4 / Real.log N := by
  have hprod := prod_primes_Icc_succ_le N
  have hle : (N : ℝ) ^ ((Finset.Icc (N + 1) (2 * N)).filter Nat.Prime).card ≤ (4 : ℝ) ^ N := by
    have h1 : (N : ℝ) ^ ((Finset.Icc (N + 1) (2 * N)).filter Nat.Prime).card ≤
        ∏ p ∈ (Finset.Icc (N + 1) (2 * N)).filter Nat.Prime, (p : ℝ) := by
      have hprod' : (∏ p ∈ (Finset.Icc (N + 1) (2 * N)).filter Nat.Prime, (N : ℝ)) ≤
          ∏ p ∈ (Finset.Icc (N + 1) (2 * N)).filter Nat.Prime, (p : ℝ) :=
        Finset.prod_le_prod₀ (fun i hi => by positivity) (fun p hp => by
          rw [Finset.mem_filter, Finset.mem_Icc] at hp
          exact_mod_cast (by omega : N ≤ p))
      rwa [Finset.prod_const] at hprod'
    have h2 : (∏ p ∈ (Finset.Icc (N + 1) (2 * N)).filter Nat.Prime, (p : ℝ)) =
        ((∏ p ∈ (Finset.Icc (N + 1) (2 * N)).filter Nat.Prime, p : ℕ) : ℝ) := by
      push_cast
      rfl
    have h3 : ((∏ p ∈ (Finset.Icc (N + 1) (2 * N)).filter Nat.Prime, p : ℕ) : ℝ) ≤ (4 : ℝ) ^ N := by
      have := Nat.cast_le (α := ℝ) |>.mpr hprod
      simpa using this
    calc (N : ℝ) ^ ((Finset.Icc (N + 1) (2 * N)).filter Nat.Prime).card
        ≤ ∏ p ∈ (Finset.Icc (N + 1) (2 * N)).filter Nat.Prime, (p : ℝ) := h1
      _ = _ := h2
      _ ≤ (4 : ℝ) ^ N := h3
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hlog : ((Finset.Icc (N + 1) (2 * N)).filter Nat.Prime).card * Real.log N ≤
      (N : ℝ) * Real.log 4 := by
    have := Real.log_le_log (by positivity) hle
    rw [Real.log_pow, Real.log_pow] at this
    exact this
  rw [le_div_iff₀ hlogN]
  linarith [hlog]

/-- **Reduction to the dyadic block.**  For `P ≥ 4`, the primes in `[P/2, P]` are contained in
`{N} ∪ {N+1, …, 2N}` with `N = ⌈P/2⌉₊`, so there are at most `1 + N log 4 / log N` of them. -/
lemma card_primesIn_half_le (P : ℝ) (hP : 4 ≤ P) :
    ((Work.BMF.primesIn (P / 2) P).card : ℝ) ≤
      1 + (⌈P / 2⌉₊ : ℝ) * Real.log 4 / Real.log (⌈P / 2⌉₊ : ℝ) := by
  have hceil2 : (2:ℕ) ≤ ⌈P / 2⌉₊ := by
    have h2 : (2:ℝ) ≤ P / 2 := by linarith
    calc (2:ℕ) = ⌈(2:ℝ)⌉₊ := by norm_num
      _ ≤ ⌈P / 2⌉₊ := Nat.ceil_mono h2
  have hsub : Work.BMF.primesIn (P / 2) P ⊆
      insert ⌈P / 2⌉₊ ((Finset.Icc (⌈P / 2⌉₊ + 1) (2 * ⌈P / 2⌉₊)).filter Nat.Prime) := by
    intro p hp
    rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hlo, hhi⟩, hprime⟩ := hp
    rw [Finset.mem_insert]
    by_cases hpN : p = ⌈P / 2⌉₊
    · exact Or.inl hpN
    · right
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, ?_⟩, hprime⟩
      have h1 : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le (by linarith)
      have h2 : P ≤ 2 * (⌈P / 2⌉₊ : ℝ) := by
        have := Nat.le_ceil (P / 2)
        linarith
      have : (p:ℝ) ≤ 2 * (⌈P / 2⌉₊ : ℝ) :=
        le_trans (Nat.cast_le.mpr hhi) (le_trans h1 h2)
      exact_mod_cast this
  calc ((Work.BMF.primesIn (P / 2) P).card : ℝ)
      ≤ ((insert ⌈P / 2⌉₊
            ((Finset.Icc (⌈P / 2⌉₊ + 1) (2 * ⌈P / 2⌉₊)).filter Nat.Prime)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (((Finset.Icc (⌈P / 2⌉₊ + 1) (2 * ⌈P / 2⌉₊)).filter Nat.Prime).card : ℝ) + 1 := by
        have := Finset.card_insert_le ⌈P / 2⌉₊
          ((Finset.Icc (⌈P / 2⌉₊ + 1) (2 * ⌈P / 2⌉₊)).filter Nat.Prime)
        exact_mod_cast this
    _ ≤ (⌈P / 2⌉₊ : ℝ) * Real.log 4 / Real.log (⌈P / 2⌉₊ : ℝ) + 1 := by
        have := card_primes_block_le ⌈P / 2⌉₊ hceil2
        linarith
    _ = 1 + (⌈P / 2⌉₊ : ℝ) * Real.log 4 / Real.log (⌈P / 2⌉₊ : ℝ) := by ring

/-- Analytic core of the large-`P` estimate.  For `t ≥ 3`,
`t² + (log 2) t + 2t ≤ 2 e^t (t(1 - log 2) - (log 2)²)`. -/
lemma key_ineq (t : ℝ) (ht : 3 ≤ t) :
    t ^ 2 + Real.log 2 * t + 2 * t ≤
      2 * Real.exp t * (t * (1 - Real.log 2) - (Real.log 2) ^ 2) := by
  have hc : Real.log 2 < 0.6932 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hc0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc2 : (Real.log 2) ^ 2 ≤ 0.4806 := by nlinarith [hc, hc0]
  have h1c : (0.3068:ℝ) ≤ 1 - Real.log 2 := by linarith
  have ht0 : 0 < t := by linarith
  have hexp3 : Real.exp 3 = (Real.exp 1) ^ 3 := by
    simpa using (Real.exp_nat_mul (1:ℝ) 3)
  have he3 : (20:ℝ) ≤ Real.exp 3 := by
    rw [hexp3]
    have hlt : (2.7182818283:ℝ) ^ 3 < (Real.exp 1) ^ 3 :=
      pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : (3:ℕ) ≠ 0)
    have hnum : (20:ℝ) < (2.7182818283:ℝ) ^ 3 := by norm_num
    linarith
  have het : 20 * (t - 2) ≤ Real.exp t := by
    have hsplit : Real.exp t = Real.exp 3 * Real.exp (t - 3) := by
      rw [← Real.exp_add]; ring_nf
    have h3'' : (1:ℝ) + (t - 3) ≤ Real.exp (t - 3) := by
      linarith [Real.add_one_le_exp (t - 3)]
    have h3n : (0:ℝ) ≤ 1 + (t - 3) := by linarith
    have h2 : (0:ℝ) ≤ Real.exp 3 := le_of_lt (Real.exp_pos 3)
    have hb : 20 * (1 + (t - 3)) ≤ Real.exp 3 * Real.exp (t - 3) :=
      mul_le_mul he3 h3'' h3n h2
    rw [hsplit]
    linarith [hb]
  have hcoef : 0.3068 * t - 0.4806 ≤ t * (1 - Real.log 2) - (Real.log 2) ^ 2 := by
    have h1 : 0.3068 * t ≤ (1 - Real.log 2) * t :=
      mul_le_mul_of_nonneg_right h1c (le_of_lt ht0)
    nlinarith [h1, hc2]
  have hpoly : t ^ 2 + 0.6932 * t + 2 * t ≤ 40 * (t - 2) * (0.3068 * t - 0.4806) := by
    nlinarith [ht]
  have hpos2 : (0:ℝ) ≤ 0.3068 * t - 0.4806 := by nlinarith [ht]
  calc t ^ 2 + Real.log 2 * t + 2 * t
      ≤ t ^ 2 + 0.6932 * t + 2 * t := by nlinarith [hc]
    _ ≤ 40 * (t - 2) * (0.3068 * t - 0.4806) := hpoly
    _ = 2 * (20 * (t - 2)) * (0.3068 * t - 0.4806) := by ring
    _ ≤ 2 * (Real.exp t) * (t * (1 - Real.log 2) - (Real.log 2) ^ 2) := by
        have hh : 20 * (t - 2) * (0.3068 * t - 0.4806) ≤
            Real.exp t * (t * (1 - Real.log 2) - (Real.log 2) ^ 2) :=
          mul_le_mul het hcoef hpos2 (le_of_lt (Real.exp_pos t))
        linarith [hh]

/-- `x ↦ x / log x` is nondecreasing on `[3, ∞)`. -/
lemma pi0_mono {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) :
    Work.BMF.pi0 a ≤ Work.BMF.pi0 b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hla : 1 ≤ Real.log a := by
    have h1 : Real.log 3 ≤ Real.log a := Real.log_le_log (by norm_num) ha
    have h2 : Real.log (Real.exp 1) < Real.log 3 :=
      Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    rw [Real.log_exp] at h2
    linarith
  have hba : 0 ≤ b - a := by linarith
  have hlogb : Real.log b = Real.log a + Real.log (b / a) := by
    rw [← Real.log_mul (ne_of_gt ha0) (by positivity : (b / a) ≠ 0)]
    field_simp
  have hlogr : Real.log (b / a) ≤ (b - a) / a := by
    have := Real.log_le_sub_one_of_pos (show 0 < b / a by positivity)
    rwa [div_sub_one (ne_of_gt ha0)] at this
  have h1 : a * Real.log (b / a) ≤ b - a := by
    have hmul : a * Real.log (b / a) ≤ a * ((b - a) / a) :=
      mul_le_mul_of_nonneg_left hlogr (le_of_lt ha0)
    have heq : a * ((b - a) / a) = b - a := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt ha0)]
    linarith [hmul, heq]
  have h3 : b - a ≤ (b - a) * Real.log a := by nlinarith [hba, hla]
  have key : a * Real.log b ≤ b * Real.log a := by
    calc a * Real.log b = a * (Real.log a + Real.log (b / a)) := by rw [hlogb]
      _ = a * Real.log a + a * Real.log (b / a) := by ring
      _ ≤ a * Real.log a + (b - a) := by linarith [h1]
      _ ≤ a * Real.log a + (b - a) * Real.log a := by linarith [h3]
      _ = b * Real.log a := by ring
  rw [Work.BMF.pi0, Work.BMF.pi0,
    div_le_div_iff₀ (Real.log_pos (by linarith)) (Real.log_pos (by linarith))]
  linarith [key]

/-- Large-`P` estimate: for `N ≥ 21`,
`1 + N log 4 / log N ≤ (2N-2) / log (2N-2)`. -/
lemma high_range_ineq (N : ℝ) (hN : 21 ≤ N) :
    1 + N * Real.log 4 / Real.log N ≤ (2 * N - 2) / Real.log (2 * N - 2) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < 2 * N - 2 := by linarith
  have hexp3le : Real.exp 3 ≤ 21 := by
    have h3 : Real.exp 3 = (Real.exp 1) ^ 3 := by simpa using (Real.exp_nat_mul (1:ℝ) 3)
    rw [h3]
    have hlt : (Real.exp 1) ^ 3 < (2.7182818286:ℝ) ^ 3 :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos 1)) (by norm_num : (3:ℕ) ≠ 0)
    have hnum : (2.7182818286:ℝ) ^ 3 < (21:ℝ) := by norm_num
    linarith
  have hlogN : 3 ≤ Real.log N :=
    (Real.le_log_iff_exp_le hN0).mpr (le_trans hexp3le hN)
  have hu : 0 < Real.log N := by linarith
  have huc : 0 < Real.log N + Real.log 2 := by
    have := Real.log_pos one_lt_two; linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hkey := key_ineq (Real.log N) hlogN
  rw [Real.exp_log hN0] at hkey
  have hstep1 : 1 + N * Real.log 4 / Real.log N ≤
      (2 * N - 2) / (Real.log N + Real.log 2) := by
    rw [hlog4]
    have hlhs : (1:ℝ) + N * (2 * Real.log 2) / Real.log N
        = (Real.log N + N * (2 * Real.log 2)) / Real.log N := by
      rw [show (1:ℝ) = Real.log N / Real.log N from (div_self (ne_of_gt hu)).symm, ← add_div]
    rw [hlhs, div_le_div_iff₀ hu huc]
    nlinarith [hkey]
  have hstep2 : (2 * N - 2) / (Real.log N + Real.log 2) ≤
      (2 * N - 2) / Real.log (2 * N - 2) := by
    have hlog_le : Real.log (2 * N - 2) ≤ Real.log N + Real.log 2 := by
      have hle : 2 * N - 2 ≤ 2 * N := by linarith
      have h := Real.log_le_log hN1 hle
      have h2 : Real.log (2 * N) = Real.log N + Real.log 2 := by
        rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hN0)]; ring
      rwa [h2] at h
    have hlogpos : 0 < Real.log (2 * N - 2) := Real.log_pos (by linarith)
    exact div_le_div_of_nonneg_left (by linarith) hlogpos hlog_le
  linarith [hstep1, hstep2]

/-- Finite verification for small scales: for `3 ≤ n ≤ 42`, the number of primes in
`[⌈n/2⌉, n]` is at most `π₀ n = n / log n`. -/
lemma low_range_finite (n : ℕ) (hn : 3 ≤ n) (hn2 : n ≤ 42) :
    (((Finset.Icc ⌈(n : ℝ) / 2⌉₊ n).filter Nat.Prime).card : ℝ) ≤ Work.BMF.pi0 n := by
  have hfin : n ^ (((Finset.Icc ⌈(n:ℝ)/2⌉₊ n).filter Nat.Prime).card) * 2 ^ n ≤ 5 ^ n := by
    interval_cases n <;> (norm_num; decide)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1r : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hcard_le : (((Finset.Icc ⌈(n:ℝ)/2⌉₊ n).filter Nat.Prime).card : ℝ) * Real.log n ≤ n := by
    have hlog : Real.log ((n:ℝ) ^ (((Finset.Icc ⌈(n:ℝ)/2⌉₊ n).filter Nat.Prime).card))
        ≤ Real.log ((5/2:ℝ) ^ n) := by
      apply Real.log_le_log (by positivity)
      have h2 : (0:ℝ) < (2:ℝ) ^ n := by positivity
      have hcast : (((n ^ (((Finset.Icc ⌈(n:ℝ)/2⌉₊ n).filter Nat.Prime).card) * 2 ^ n : ℕ)) : ℝ)
          ≤ ((5 ^ n : ℕ) : ℝ) := by exact_mod_cast hfin
      push_cast at hcast
      rw [div_pow, le_div_iff₀ h2]
      linarith [hcast]
    rw [Real.log_pow, Real.log_pow] at hlog
    have h52 : Real.log (5/2) ≤ 1 := by
      have h := Real.log_le_log (by norm_num : (0:ℝ) < 5/2)
        (by linarith [Real.exp_one_gt_d9] : (5/2:ℝ) ≤ Real.exp 1)
      rwa [Real.log_exp] at h
    have := mul_le_mul_of_nonneg_left h52 (le_of_lt hn0)
    linarith [hlog, this]
  rw [Work.BMF.pi0, le_div_iff₀ (Real.log_pos hn1r)]
  linarith [hcard_le]

/-- Small-`P` case: `1 < P ≤ 42`. -/
lemma low_range (P : ℝ) (hP1 : 1 < P) (hP2 : P ≤ 42) :
    ((Work.BMF.primesIn (P / 2) P).card : ℝ) ≤ Work.BMF.pi0 P := by
  have hP0 : 0 < P := by linarith
  have hnle : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le (le_of_lt hP0)
  rcases lt_or_ge ⌊P⌋₊ 3 with hn3 | hn3
  · have hsub : Work.BMF.primesIn (P / 2) P ⊆ ({2} : Finset ℕ) := by
      intro p hp
      rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨hlo, hhi⟩, hprime⟩ := hp
      rw [Finset.mem_singleton]
      exact le_antisymm (by omega) hprime.two_le
    have hcard : ((Work.BMF.primesIn (P / 2) P).card : ℝ) ≤ 1 := by
      have hc : (Work.BMF.primesIn (P / 2) P).card ≤ 1 := by
        have := Finset.card_le_card hsub
        simpa using this
      exact_mod_cast hc
    have hpi0 : 1 ≤ Work.BMF.pi0 P := by
      rw [Work.BMF.pi0, le_div_iff₀ (Real.log_pos hP1)]
      have := Real.log_le_sub_one_of_pos hP0
      linarith
    linarith
  · have hn42 : ⌊P⌋₊ ≤ 42 := by
      have : (⌊P⌋₊ : ℝ) ≤ 42 := le_trans hnle hP2
      exact_mod_cast this
    have hsub : Work.BMF.primesIn (P / 2) P ⊆
        (Finset.Icc ⌈(⌊P⌋₊ : ℝ) / 2⌉₊ ⌊P⌋₊).filter Nat.Prime := by
      intro p hp
      rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨hlo, hhi⟩, hprime⟩ := hp
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, hhi⟩, hprime⟩
      calc ⌈(⌊P⌋₊ : ℝ) / 2⌉₊ ≤ ⌈P / 2⌉₊ := Nat.ceil_mono (by linarith [hnle])
        _ ≤ p := hlo
    have hcard : ((Work.BMF.primesIn (P / 2) P).card : ℝ) ≤
        (((Finset.Icc ⌈(⌊P⌋₊ : ℝ) / 2⌉₊ ⌊P⌋₊).filter Nat.Prime).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hfin := low_range_finite ⌊P⌋₊ hn3 hn42
    have hmono : Work.BMF.pi0 (⌊P⌋₊ : ℝ) ≤ Work.BMF.pi0 P :=
      pi0_mono (by exact_mod_cast hn3) hnle
    linarith [hcard, hfin, hmono]

theorem primesIn_half_card_le_pi0 (P : ℝ) (hP : 1 < P) :
    ((Work.BMF.primesIn (P / 2) P).card : ℝ) ≤ Work.BMF.pi0 P := by
  rcases lt_or_ge P 42 with hP42 | hP42
  · exact low_range P hP (le_of_lt hP42)
  · have hP4 : 4 ≤ P := by linarith
    have hN21 : 21 ≤ ⌈P / 2⌉₊ := by
      have h2 : (21:ℝ) ≤ P / 2 := by linarith
      calc (21:ℕ) = ⌈(21:ℝ)⌉₊ := by norm_num
        _ ≤ ⌈P / 2⌉₊ := Nat.ceil_mono h2
    have hcard := card_primesIn_half_le P hP4
    have hhi := high_range_ineq (⌈P / 2⌉₊ : ℝ) (by exact_mod_cast hN21)
    have hN_le : (2 * (⌈P / 2⌉₊ : ℝ) - 2) ≤ P := by
      have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ P/2 by linarith)
      linarith
    have hlow3 : (3:ℝ) ≤ 2 * (⌈P / 2⌉₊ : ℝ) - 2 := by
      have : (21:ℝ) ≤ (⌈P / 2⌉₊ : ℝ) := by exact_mod_cast hN21
      linarith
    have hmono := pi0_mono hlow3 hN_le
    rw [Work.BMF.pi0, Work.BMF.pi0] at hmono
    rw [Work.BMF.pi0]
    linarith [hcard, hhi, hmono]

end Work.N8
