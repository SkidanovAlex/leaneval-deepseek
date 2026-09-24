import Mathlib
import Submission.Work.Chen.SwitchDefs
import Submission.Work.ChenPlan.H1.Defs
import Submission.Commons.NumberTheory.Sieve.prod_one_add_inv_prime_le_log_of_two_le
import Submission.Work.ChenPlan.H1.prod_primes_one_add_nine_div_le
import Submission.Work.ChenPlan.H1.prod_primes_one_add_nine_div_pred_le
import Submission.Work.ChenPlan.H1.sum_divisors_primeFactors_prod_le

/-!
# The trivial `9^{ω(d)}`-weighted bound for Chen's sieve remainder

This file proves the elementary (Bombieri--Vinogradov-independent) bound

`Σ_{d ∣ P, d < D} 9^{ω(d)} |r_D(x)| ≤ C · x · (log x)^10`

for the shifted-prime remainder `r_D(x) = θ_D(x) - x/φ(D)` of Chen's `h1`, valid for every primorial
`P = oddPrimLt M` and every level `D ≤ √x`.  It is the input `TrivInput` of
`Submission/Work/ChenPlan/H1/RemBound.lean`.

The proof is the trivial one: `|r_d| ≤ θ_d(x) + x/φ(d)`, `θ_d(x) ≤ (2x/d)·log x` (there are at most
`(x+2)/d` primes `p ≤ x` with `d ∣ p+2`), and the `9^{ω(d)}`-weighted divisor sums are dominated by
Euler products,
`Σ_{d ∣ P, d ≤ N} 9^{ω(d)}/d ≤ ∏_{p ≤ N} (1 + 9/p) ≤ C (log N)^9`,
`Σ_{d ∣ P, d ≤ N} 9^{ω(d)}/φ(d) ≤ ∏_{p ≤ N} (1 + 9/(p-1)) ≤ C (log N)^9`.
-/

open Finset
open scoped BigOperators

namespace Work.ChenPlan.H1

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight

/-! ## Elementary facts about `thetaD` -/

/-- `thetaD x d` is a sum of logarithms of primes, hence nonnegative. -/
lemma thetaD_nonneg (x d : ℕ) : 0 ≤ thetaD x d := by
  unfold thetaD
  refine Finset.sum_nonneg (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  exact Real.log_nonneg (by
    have := hp.2.1.two_le
    exact_mod_cast (by omega : 1 ≤ p))

/-- The number of primes `p ≤ x` with `d ∣ p + 2` is at most `(x + 2) / d`. -/
lemma card_prime_filter_dvd_le (x d : ℕ) (_hd : 1 ≤ d) :
    ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime ∧ d ∣ p + 2)).card
      ≤ (x + 2) / d := by
  set S : Finset ℕ := (Finset.range (x + 1)).filter (fun p : ℕ => p.Prime ∧ d ∣ p + 2) with hS
  have hmaps : ∀ p ∈ S, (p + 2) / d ∈ Finset.Icc 1 ((x + 2) / d) := by
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpx, _hpp, hpd⟩ := hp
    rw [Finset.mem_Icc]
    have hpos : 0 < (p + 2) / d := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      have hc := Nat.mul_div_cancel' hpd
      rw [h0, mul_zero] at hc
      omega
    exact ⟨hpos, Nat.div_le_div_right (by omega : p + 2 ≤ x + 2)⟩
  have hinj : Set.InjOn (fun p : ℕ => (p + 2) / d) (↑S : Set ℕ) := by
    intro p hp q hq heq
    have hp' : d ∣ p + 2 := by
      rw [Finset.mem_coe, hS, Finset.mem_filter] at hp
      exact hp.2.2
    have hq' : d ∣ q + 2 := by
      rw [Finset.mem_coe, hS, Finset.mem_filter] at hq
      exact hq.2.2
    have heq' : (p + 2) / d = (q + 2) / d := heq
    have h2 : p + 2 = q + 2 := by
      rw [← Nat.mul_div_cancel' hp', ← Nat.mul_div_cancel' hq', heq']
    omega
  calc S.card = (S.image (fun p : ℕ => (p + 2) / d)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 ((x + 2) / d)).card := by
        refine Finset.card_le_card ?_
        rintro k hk
        rw [Finset.mem_image] at hk
        obtain ⟨p, hp, rfl⟩ := hk
        exact hmaps p hp
    _ = (x + 2) / d := by rw [Nat.card_Icc]; simp

/-- `θ_d(x) ≤ (2x/d)·log x` for `x ≥ 2`, `d ≥ 1`. -/
lemma thetaD_le (x d : ℕ) (hx : 2 ≤ x) (hd : 1 ≤ d) :
    thetaD x d ≤ (2 * (x : ℝ) / (d : ℝ)) * Real.log (x : ℝ) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hlogx : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  have hlog_le : ∀ p ∈ (Finset.range (x + 1)).filter (fun p : ℕ => p.Prime ∧ d ∣ p + 2),
      Real.log (p : ℝ) ≤ Real.log (x : ℝ) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    have hp1 : (0 : ℝ) < (p : ℝ) := by
      have : 2 ≤ p := hp.2.1.two_le
      exact_mod_cast (by omega : 0 < p)
    have hple : (p : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : p ≤ x)
    exact Real.log_le_log hp1 hple
  have hcard := card_prime_filter_dvd_le x d hd
  calc thetaD x d
      = ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime ∧ d ∣ p + 2)).sum
          (fun p => Real.log (p : ℝ)) := rfl
    _ ≤ ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime ∧ d ∣ p + 2)).sum
          (fun _ => Real.log (x : ℝ)) := Finset.sum_le_sum hlog_le
    _ = (((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime ∧ d ∣ p + 2)).card : ℝ)
          * Real.log (x : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((x + 2 : ℕ) : ℝ) / (d : ℝ) * Real.log (x : ℝ) := by
        have h1 : ((((Finset.range (x + 1)).filter
            (fun p : ℕ => p.Prime ∧ d ∣ p + 2)).card : ℕ) : ℝ) ≤ (((x + 2) / d : ℕ) : ℝ) := by
          exact_mod_cast hcard
        have h2 : (((x + 2) / d : ℕ) : ℝ) ≤ ((x + 2 : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
        exact mul_le_mul_of_nonneg_right (le_trans h1 h2) hlogx
    _ ≤ (2 * (x : ℝ) / (d : ℝ)) * Real.log (x : ℝ) := by
        have hnum : ((x + 2 : ℕ) : ℝ) ≤ 2 * (x : ℝ) := by
          exact_mod_cast (by omega : x + 2 ≤ 2 * x)
        have := div_le_div_of_nonneg_right hnum (le_of_lt hdpos)
        exact mul_le_mul_of_nonneg_right this hlogx

/-! ## The per-divisor identities for the weights `9^{ω(d)}/d` and `9^{ω(d)}/φ(d)` -/

/-- For squarefree `d`, `9^{ω(d)}/d = ∏_{p ∣ d} 9/p`. -/
lemma nine_pow_card_div_eq_prod_primeFactors {d : ℕ} (hd : Squarefree d) :
    (9 : ℝ) ^ d.primeFactors.card / (d : ℝ) = ∏ p ∈ d.primeFactors, (9 / (p : ℝ)) := by
  have hprod : (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  rw [← hprod, ← Finset.prod_const (s := d.primeFactors) (9 : ℝ), ← Finset.prod_div_distrib]

/-- For `d ≠ 0`, `9^{ω(d)}/φ(d) ≤ ∏_{p ∣ d} 9/(p - 1)`. -/
lemma nine_pow_card_div_totient_le {d : ℕ} (hd : d ≠ 0) :
    (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ)
      ≤ ∏ p ∈ d.primeFactors, (9 / ((p : ℝ) - 1)) := by
  have hR1 : 1 ≤ ∏ p ∈ d.primeFactors, (p - 1) := by
    refine Finset.one_le_prod₀ (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Nat.mem_primeFactors.mp hp).1.two_le
    omega
  have hcastR : ((∏ p ∈ d.primeFactors, (p - 1) : ℕ) : ℝ)
      = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp1 : 1 ≤ p := le_trans (by norm_num) (Nat.mem_primeFactors.mp hp).1.two_le
    rw [Nat.cast_sub hp1, Nat.cast_one]
  have hradpos : 0 < ∏ p ∈ d.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.mem_primeFactors.mp hp).1.pos)
  have hk1 : 1 ≤ d / ∏ p ∈ d.primeFactors, p :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) (Nat.prod_primeFactors_dvd d)) hradpos
  have hphi : ((∏ p ∈ d.primeFactors, (p - 1) : ℕ) : ℝ) ≤ (Nat.totient d : ℝ) := by
    rw [Nat.totient_eq_div_primeFactors_mul d, Nat.cast_mul, hcastR]
    have hk1R : (1 : ℝ) ≤ ((d / ∏ p ∈ d.primeFactors, p : ℕ) : ℝ) := by exact_mod_cast hk1
    have hRnn : (0 : ℝ) ≤ ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) :=
      Finset.prod_nonneg (fun p hp => by
        have hp2 : 2 ≤ p := (Nat.mem_primeFactors.mp hp).1.two_le
        have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
        linarith)
    nlinarith
  have hRpos : (0 : ℝ) < ((∏ p ∈ d.primeFactors, (p - 1) : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR1)
  calc (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ)
      ≤ (9 : ℝ) ^ d.primeFactors.card
          / ((∏ p ∈ d.primeFactors, (p - 1) : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hRpos hphi
    _ = ∏ p ∈ d.primeFactors, (9 / ((p : ℝ) - 1)) := by
        rw [hcastR, ← Finset.prod_const (s := d.primeFactors) (9 : ℝ), ← Finset.prod_div_distrib]

/-! ## Euler-product domination of the divisor sums -/

/-- The `9^{ω(d)}/d`-weighted divisor sum of a squarefree `P` is dominated by the Euler product. -/
lemma sum_div_nine_pow_div_le (P N : ℕ) (hP : Squarefree P) :
    (∑ d ∈ P.divisors.filter (fun d : ℕ => d ≤ N), (9 : ℝ) ^ d.primeFactors.card / (d : ℝ))
      ≤ ∏ p ∈ P.primeFactors.filter (fun p : ℕ => p ≤ N), (1 + 9 / (p : ℝ)) := by
  have h : ∀ d ∈ P.divisors.filter (fun d : ℕ => d ≤ N),
      (9 : ℝ) ^ d.primeFactors.card / (d : ℝ) = ∏ p ∈ d.primeFactors, (9 / (p : ℝ)) := by
    intro d hd
    exact nine_pow_card_div_eq_prod_primeFactors
      (hP.squarefree_of_dvd (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1)
  rw [Finset.sum_congr rfl h]
  exact sum_divisors_primeFactors_prod_le P N (fun p => 9 / (p : ℝ)) hP
    (fun p => div_nonneg (by norm_num) (Nat.cast_nonneg p))

/-- The `9^{ω(d)}/φ(d)`-weighted divisor sum of a squarefree `P` is dominated by the Euler product. -/
lemma sum_div_nine_pow_totient_le (P N : ℕ) (hP : Squarefree P) :
    (∑ d ∈ P.divisors.filter (fun d : ℕ => d ≤ N),
        (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ))
      ≤ ∏ p ∈ P.primeFactors.filter (fun p : ℕ => p ≤ N), (1 + 9 / ((p : ℝ) - 1)) := by
  set c : ℕ → ℝ := fun p => if 2 ≤ p then 9 / ((p : ℝ) - 1) else 0 with hcdef
  have hc_nn : ∀ p, 0 ≤ c p := by
    intro p
    simp only [hcdef]
    by_cases h : 2 ≤ p
    · rw [if_pos h]
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    · rw [if_neg h]
  have hc_prime : ∀ p, Nat.Prime p → c p = 9 / ((p : ℝ) - 1) := by
    intro p hp
    simp only [hcdef, if_pos hp.two_le]
  have h : ∀ d ∈ P.divisors.filter (fun d : ℕ => d ≤ N),
      (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ)
        ≤ ∏ p ∈ d.primeFactors, c p := by
    intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1).ne'
    have hineq := nine_pow_card_div_totient_le hd0
    have hprod : (∏ p ∈ d.primeFactors, (9 / ((p : ℝ) - 1)))
        = ∏ p ∈ d.primeFactors, c p := by
      refine Finset.prod_congr rfl (fun p hp => ?_)
      rw [hc_prime p (Nat.mem_primeFactors.mp hp).1]
    rwa [hprod] at hineq
  refine le_trans (Finset.sum_le_sum h) ?_
  refine le_trans (sum_divisors_primeFactors_prod_le P N c hP hc_nn) ?_
  refine Finset.prod_le_prod₀ (fun p _ => by
    have := hc_nn p
    linarith) (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  rw [hc_prime p (Nat.mem_primeFactors.mp hp.1).1]

/-! ## The target bound -/

theorem weighted_triv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop, ∀ (M : ℕ) (D : ℝ),
      4 ≤ D → D ≤ Real.sqrt (x : ℝ) →
      ∑ d ∈ (Commons.NumberTheory.Chen.ChenEight.oddPrimLt M).divisors.filter
            (fun d : ℕ => (d : ℝ) < D),
          (9 : ℝ) ^ d.primeFactors.card * |Commons.NumberTheory.Chen.ChenEight.rD x d|
        ≤ C * (x : ℝ) * (Real.log (x : ℝ)) ^ 10 := by
  obtain ⟨C1, hC1pos, hC1⟩ := prod_primes_one_add_nine_div_le
  obtain ⟨C2, hC2pos, hC2⟩ := prod_primes_one_add_nine_div_pred_le
  refine ⟨2 * C1 + C2 + 1, by linarith, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 16] with x hx16
  intro M D hD4 hDle
  set P : ℕ := oddPrimLt M with hPdef
  set N : ℕ := ⌊Real.sqrt (x : ℝ)⌋₊ with hNdef
  set L : ℝ := Real.log (x : ℝ) with hLdef
  have hx2 : 2 ≤ x := by omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have h16R : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx16
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]; norm_num
    have h2 : (1 : ℝ) ≤ Real.log (16 : ℝ) := by rw [h16]; nlinarith [Real.log_two_gt_d9]
    exact le_trans h2 (Real.log_le_log (by norm_num) h16R)
  have hN2 : 2 ≤ N := by
    rw [hNdef, Nat.le_floor_iff (Real.sqrt_nonneg _)]
    have h4 : (4 : ℝ) ≤ Real.sqrt (x : ℝ) := by
      have hsqrt16 : Real.sqrt (16 : ℝ) = 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      calc (4 : ℝ) = Real.sqrt 16 := hsqrt16.symm
        _ ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt h16R
    have : (2 : ℝ) ≤ Real.sqrt (x : ℝ) := by linarith
    exact_mod_cast this
  have hNx : (N : ℝ) ≤ (x : ℝ) := by
    rw [hNdef]
    refine le_trans (Nat.floor_le (Real.sqrt_nonneg _)) ?_
    rw [Real.sqrt_le_iff]
    exact ⟨le_of_lt hxpos, by nlinarith [h16R]⟩
  have hlogNle : Real.log (N : ℝ) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by positivity) hNx
  have hPsq : Squarefree P := by rw [hPdef]; exact oddPrimLt_squarefree M
  set F : Finset ℕ := P.divisors.filter (fun d : ℕ => (d : ℝ) < D) with hFdef
  set G : Finset ℕ := P.divisors.filter (fun d : ℕ => d ≤ N) with hGdef
  have hFG : F ⊆ G := by
    intro d hd
    rw [hFdef, Finset.mem_filter] at hd
    rw [hGdef, Finset.mem_filter]
    refine ⟨hd.1, ?_⟩
    rw [hNdef, Nat.le_floor_iff (Real.sqrt_nonneg _)]
    exact le_of_lt (lt_of_lt_of_le hd.2 hDle)
  -- Step 1: split each summand into the `theta` part and the totient part
  have hterm : ∀ d ∈ F, (9 : ℝ) ^ d.primeFactors.card * |rD x d|
      ≤ (9 : ℝ) ^ d.primeFactors.card * thetaD x d
        + (9 : ℝ) ^ d.primeFactors.card * ((x : ℝ) / (Nat.totient d : ℝ)) := by
    intro d _
    have hq : 0 ≤ (x : ℝ) / (Nat.totient d : ℝ) :=
      div_nonneg (le_of_lt hxpos) (Nat.cast_nonneg _)
    have h1 : (9 : ℝ) ^ d.primeFactors.card * |rD x d|
        ≤ (9 : ℝ) ^ d.primeFactors.card
          * (thetaD x d + (x : ℝ) / (Nat.totient d : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [rD, abs_sub_le_iff]
      constructor <;> linarith [thetaD_nonneg x d]
    calc (9 : ℝ) ^ d.primeFactors.card * |rD x d|
        ≤ (9 : ℝ) ^ d.primeFactors.card
          * (thetaD x d + (x : ℝ) / (Nat.totient d : ℝ)) := h1
      _ = _ := by ring
  have hsplit : ∑ d ∈ F, (9 : ℝ) ^ d.primeFactors.card * |rD x d|
      ≤ (∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card * thetaD x d)
        + ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card * ((x : ℝ) / (Nat.totient d : ℝ)) := by
    calc ∑ d ∈ F, (9 : ℝ) ^ d.primeFactors.card * |rD x d|
        ≤ ∑ d ∈ F, ((9 : ℝ) ^ d.primeFactors.card * thetaD x d
            + (9 : ℝ) ^ d.primeFactors.card * ((x : ℝ) / (Nat.totient d : ℝ))) :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ d ∈ G, ((9 : ℝ) ^ d.primeFactors.card * thetaD x d
            + (9 : ℝ) ^ d.primeFactors.card * ((x : ℝ) / (Nat.totient d : ℝ))) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hFG (fun d _ _ => ?_)
          exact add_nonneg (mul_nonneg (by positivity) (thetaD_nonneg x d))
            (mul_nonneg (by positivity)
              (div_nonneg (le_of_lt hxpos) (Nat.cast_nonneg _)))
      _ = _ := Finset.sum_add_distrib
  -- Step 2a: the `theta` part
  have hθ : ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card * thetaD x d
      ≤ 2 * (x : ℝ) * L * (C1 * L ^ 9) := by
    have h1 : ∀ d ∈ G, (9 : ℝ) ^ d.primeFactors.card * thetaD x d
        ≤ (9 : ℝ) ^ d.primeFactors.card * (2 * (x : ℝ) * L / (d : ℝ)) := by
      intro d hd
      have hdG : d ∈ P.divisors.filter (fun d : ℕ => d ≤ N) := by
        rw [← hGdef]; exact hd
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hdG).1
      have h := thetaD_le x d hx2 hd1
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have heq : (2 * (x : ℝ) / (d : ℝ)) * Real.log (x : ℝ)
          = 2 * (x : ℝ) * L / (d : ℝ) := by rw [hLdef]; ring
      rw [heq] at h; exact h
    calc ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card * thetaD x d
        ≤ ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card * (2 * (x : ℝ) * L / (d : ℝ)) :=
          Finset.sum_le_sum h1
      _ = 2 * (x : ℝ) * L * ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          ring
      _ ≤ 2 * (x : ℝ) * L * (∏ p ∈ P.primeFactors.filter (fun p : ℕ => p ≤ N),
            (1 + 9 / (p : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := sum_div_nine_pow_div_le P N hPsq
          rwa [hGdef]
      _ ≤ 2 * (x : ℝ) * L * (∏ p ∈ Nat.primesBelow (N + 1), (1 + 9 / (p : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.prod_le_prod_of_subset_of_one_le₀ ?_ (fun p _ => ?_) (fun p _ _ => ?_)
          · intro p hp
            rw [Finset.mem_filter] at hp
            rw [Nat.mem_primesBelow]
            exact ⟨by omega, (Nat.mem_primeFactors.mp hp.1).1⟩
          · have h9nn : (0 : ℝ) ≤ 9 / (p : ℝ) := div_nonneg (by norm_num) (by positivity)
            linarith
          · have h9nn : (0 : ℝ) ≤ 9 / (p : ℝ) := div_nonneg (by norm_num) (by positivity)
            linarith
      _ ≤ 2 * (x : ℝ) * L * (C1 * L ^ 9) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h := hC1 N hN2
          refine le_trans h (mul_le_mul_of_nonneg_left ?_ (le_of_lt hC1pos))
          exact pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) hlogNle 9
  -- Step 2b: the totient part
  have hφ : ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card * ((x : ℝ) / (Nat.totient d : ℝ))
      ≤ (x : ℝ) * (C2 * L ^ 9) := by
    calc ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card * ((x : ℝ) / (Nat.totient d : ℝ))
        = (x : ℝ) * ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          ring
      _ ≤ (x : ℝ) * (∏ p ∈ P.primeFactors.filter (fun p : ℕ => p ≤ N),
            (1 + 9 / ((p : ℝ) - 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hxpos)
          have := sum_div_nine_pow_totient_le P N hPsq
          rwa [hGdef]
      _ ≤ (x : ℝ) * (∏ p ∈ Nat.primesBelow (N + 1), (1 + 9 / ((p : ℝ) - 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hxpos)
          refine Finset.prod_le_prod_of_subset_of_one_le₀ ?_ (fun p hp => ?_) (fun p hp _ => ?_)
          · intro p hp
            rw [Finset.mem_filter] at hp
            rw [Nat.mem_primesBelow]
            exact ⟨by omega, (Nat.mem_primeFactors.mp hp.1).1⟩
          · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
              exact_mod_cast (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.two_le
            have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
            have h9nn : (0 : ℝ) ≤ 9 / ((p : ℝ) - 1) := div_nonneg (by norm_num) (le_of_lt hp1)
            linarith
          · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
              exact_mod_cast (Nat.two_le_of_mem_primesBelow hp)
            have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
            have h9nn : (0 : ℝ) ≤ 9 / ((p : ℝ) - 1) := div_nonneg (by norm_num) (le_of_lt hp1)
            linarith
      _ ≤ (x : ℝ) * (C2 * L ^ 9) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hxpos)
          have h := hC2 N hN2
          refine le_trans h (mul_le_mul_of_nonneg_left ?_ (le_of_lt hC2pos))
          exact pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) hlogNle 9
  -- Step 3: combine
  calc ∑ d ∈ F, (9 : ℝ) ^ d.primeFactors.card * |rD x d|
      ≤ (∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card * thetaD x d)
        + ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card * ((x : ℝ) / (Nat.totient d : ℝ)) := hsplit
    _ ≤ 2 * (x : ℝ) * L * (C1 * L ^ 9) + (x : ℝ) * (C2 * L ^ 9) := add_le_add hθ hφ
    _ ≤ (2 * C1 + C2 + 1) * (x : ℝ) * (Real.log (x : ℝ)) ^ 10 := by
        rw [← hLdef]
        have hL9L10 : L ^ 9 ≤ L ^ 10 := by nlinarith [hL1, pow_nonneg (le_trans zero_le_one hL1) 9]
        have e1 : 2 * (x : ℝ) * L * (C1 * L ^ 9) = 2 * C1 * ((x : ℝ) * L ^ 10) := by ring
        have e2 : (x : ℝ) * (C2 * L ^ 9) = C2 * ((x : ℝ) * L ^ 9) := by ring
        have e3 : (2 * C1 + C2 + 1) * (x : ℝ) * L ^ 10
            = (2 * C1 + C2 + 1) * ((x : ℝ) * L ^ 10) := by ring
        rw [e1, e2, e3]
        have h2 : C2 * ((x : ℝ) * L ^ 9) ≤ C2 * ((x : ℝ) * L ^ 10) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL9L10 (le_of_lt hxpos))
            (le_of_lt hC2pos)
        have h3 : 0 ≤ (x : ℝ) * L ^ 10 := by positivity
        nlinarith [h2, h3, hC1pos, hxpos]

end

end Work.ChenPlan.H1
