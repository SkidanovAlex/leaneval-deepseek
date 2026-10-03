import Mathlib
import Submission.Work.Analysis.IonescuWainger.Height

/-!
# `(ℚ/ℤ)_{≤l}` is non-decreasing in `l`, for **every** `ρ > 0`

The workspace lemma `Work.Analysis.IonescuWainger.iwArithFreqs_mono` proves

`iwArithFreqs ρ l ⊆ iwArithFreqs ρ l'`  for `l ≤ l'`

under the additional hypothesis `ρ ≤ 1`.  This file removes that hypothesis.

Throughout, `iwP ρ l` is `[2^l]` for `l ≤ C⁰_ρ` and the concrete Ionescu–Wainger set
`iwPconcrete ρ l` for `l > C⁰_ρ`, and `iwArithFreqs ρ l = ⋃_{q ∈ iwP ρ l} {a/q}`.
The inclusion `iwP ρ l ⊆ iwP ρ (l+1)` splits into three cases:

* `l + 1 ≤ C⁰_ρ`: both sets are `[1, 2^l] ⊆ [1, 2^{l+1}]`;
* `l = C⁰_ρ`: one needs the inclusion `[2^l] ⊆ P_{≤l+1}`, i.e. `iwPconcrete_contains_range`;
* `C⁰_ρ < l`: both sets are concrete, and `iwPconcrete_mono` is proved for **all** `ρ ∈ ℝ`.

So the only place where `ρ ≤ 1` enters is the arithmetic of Appendix A establishing
`[2^l] ⊆ iwPconcrete ρ l` for `l ≥ C⁰_ρ`.  There the hypothesis was used only to obtain
`ε_ρ = ρD_ρ/2 - 1 ≤ 1/2`, which in turn was used only to produce the lower bound `N_0^{(l)} ≥ 8`
needed by `prime_rpow_le` (whose proof actually never uses `ε ≤ 1/2`).  But
`C⁰_ρ = ⌈(2/ρ)(1+ε_ρ)/ε_ρ⌉₊ + ⌈10/ρ⌉₊ + 100 ≥ 10/ρ + 100` already forces `ρl/2 ≥ 5`, hence
`N_0^{(l)} > 2^5 > 8`, for **every** `ρ > 0`.  In the regime `ε_ρ > 1/2` one then applies
`prime_rpow_le` with `ε := 1/2 ≤ ε_ρ` (which gives the weaker, but sufficient, bound
`p^{3⌊N_0/p⌋/2} ≤ p^{(1+ε_ρ)⌊N_0/p⌋}`), and in the regime `ε_ρ ≤ 1/2` one applies it directly.

This file therefore reproduces, without the hypothesis `ρ ≤ 1`, the chain
`iwC0SmallPrimeExp` → `iwPrimeRangeCard`/`iwLow_dvd_iwQ0`/`iwHigh_mem_iwW` →
`iwPconcrete_contains_range` → `iwP_succ` → `iwArithFreqs_mono`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.KMTPlan.A6.LowModApproxBoundedH

open Work.Analysis.IonescuWainger

/-! ## The Ionescu–Wainger parameters -/

private theorem iwD_gt (ρ : ℝ) : 2 / ρ < (iwD ρ : ℝ) := by
  rw [iwD, Nat.cast_add, Nat.cast_one]
  exact Nat.lt_floor_add_one _

/-- `ε_ρ = ρD_ρ/2 - 1 > 0`, for every `ρ > 0`. -/
private theorem iwEps_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < iwEps ρ := by
  rw [iwEps]
  have h2 := mul_lt_mul_of_pos_left (iwD_gt ρ) hρ
  rw [mul_comm ρ (2 / ρ), div_mul_cancel₀ 2 (ne_of_gt hρ)] at h2
  linarith

/-- The identity `(2/ρ)(1 + ε_ρ) = D_ρ`. -/
private theorem iwD_eq_ratio {ρ : ℝ} (hρ : 0 < ρ) : (2 / ρ) * (1 + iwEps ρ) = (iwD ρ : ℝ) := by
  rw [iwEps]; field_simp; ring

/-- The lower bound on the threshold driving the estimate:
`(2/ρ)(1 + ε_ρ)/ε_ρ ≤ C⁰_ρ`. -/
private theorem iwC0_lower (ρ : ℝ) : (2 / ρ) * ((1 + iwEps ρ) / iwEps ρ) ≤ (iwC0 ρ : ℝ) := by
  rw [iwC0]
  have h := Nat.le_ceil ((2 / ρ) * ((1 + iwEps ρ) / iwEps ρ))
  push_cast
  linarith

/-- `C⁰_ρ ≥ 10/ρ + 100` (the `+ 100` in the definition of `iwC0`). -/
private theorem iwC0_ge (ρ : ℝ) : (10 / ρ : ℝ) + 100 ≤ (iwC0 ρ : ℝ) := by
  rw [iwC0]; push_cast
  have h := Nat.le_ceil (10 / ρ)
  have h2 : (0 : ℝ) ≤ (⌈(2 / ρ) * ((1 + iwEps ρ) / iwEps ρ)⌉₊ : ℝ) := Nat.cast_nonneg _
  linarith

/-- For `l ≥ C⁰_ρ` one has `N_0^{(l)} ≥ 8`: indeed `ρl/2 ≥ 5`. -/
private theorem eight_le_iwN0 {ρ : ℝ} (hρ : 0 < ρ) {l : ℕ} (hl : iwC0 ρ ≤ l) :
    8 ≤ iwN0 ρ l := by
  have hC0 : (10 / ρ : ℝ) + 100 ≤ (l : ℝ) := by
    have h1 : (10 / ρ : ℝ) + 100 ≤ (iwC0 ρ : ℝ) := iwC0_ge ρ
    have h2 : ((iwC0 ρ : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  have hρl : 10 + 100 * ρ ≤ ρ * (l : ℝ) := by
    have h1 : ρ * (10 / ρ + 100) ≤ ρ * (l : ℝ) := mul_le_mul_of_nonneg_left hC0 hρ.le
    have h2 : ρ * (10 / ρ + 100) = 10 + 100 * ρ := by
      rw [mul_add, mul_comm ρ (10 / ρ), div_mul_cancel₀ 10 (ne_of_gt hρ)]
      ring
    rwa [h2] at h1
  have h3 : (3 : ℝ) ≤ ρ * (l : ℝ) / 2 := by linarith
  have h23 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := by
    calc (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := h23.symm
      _ ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
  have : (8 : ℝ) < (iwN0 ρ l : ℝ) := lt_of_le_of_lt h8 (IwCont.iwN0_gt ρ l)
  exact le_of_lt (Nat.cast_lt.mp this)

/-! ## Small primes have bounded exponent, for every `ρ > 0` -/

/-- **Small primes have bounded exponent** (Appendix A, without the hypothesis `ρ ≤ 1`).
In the regime `l ≥ C⁰_ρ`, any prime power `p ^ j` with `p ≤ N_0^{(l)}` prime and `p ^ j ≤ 2 ^ l`
satisfies `j ≤ D_ρ · v_p(N_0^{(l)}!)`. -/
private theorem iwC0SmallPrimeExp_gen {ρ : ℝ} (hρ : 0 < ρ) {l q p j : ℕ}
    (hl : iwC0 ρ ≤ l) (hq : q ≤ 2 ^ l) (hp : p.Prime) (hpN : p ≤ iwN0 ρ l)
    (hpj : p ^ j ≤ q) : j ≤ iwD ρ * (iwN0 ρ l).factorial.factorization p := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hεpos : 0 < iwEps ρ := iwEps_pos hρ
  have hNgt : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) < (iwN0 ρ l : ℝ) := IwCont.iwN0_gt ρ l
  -- `l ≥ C⁰_ρ` gives `(2/ρ)(1+ε_ρ)/ε_ρ ≤ l`, hence `(1+ε_ρ)/ε_ρ ≤ ρl/2`
  have hl' : (2 / ρ) * ((1 + iwEps ρ) / iwEps ρ) ≤ (l : ℝ) := by
    have h1 : (2 / ρ) * ((1 + iwEps ρ) / iwEps ρ) ≤ (iwC0 ρ : ℝ) := iwC0_lower ρ
    have h2 : ((iwC0 ρ : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  have hratio : (1 + iwEps ρ) / iwEps ρ ≤ ρ * (l : ℝ) / 2 := by
    have h2 : (0 : ℝ) < ρ / 2 := by linarith
    have h3 := mul_le_mul_of_nonneg_left hl' h2.le
    have heq : (ρ / 2) * ((2 / ρ) * ((1 + iwEps ρ) / iwEps ρ)) = (1 + iwEps ρ) / iwEps ρ := by
      field_simp
    calc (1 + iwEps ρ) / iwEps ρ = (ρ / 2) * ((2 / ρ) * ((1 + iwEps ρ) / iwEps ρ)) := heq.symm
      _ ≤ (ρ / 2) * (l : ℝ) := h3
      _ = ρ * (l : ℝ) / 2 := by ring
  have hN8 : 8 ≤ iwN0 ρ l := eight_le_iwN0 hρ hl
  -- the hypothesis `2^{(1+ε_ρ)/ε_ρ} ≤ N_0^{(l)}` of `prime_rpow_le`
  have hN' : (2 : ℝ) ^ ((1 + iwEps ρ) / iwEps ρ) ≤ (iwN0 ρ l : ℝ) :=
    le_of_lt (lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le (by norm_num) hratio) hNgt)
  have hNp : (iwN0 ρ l : ℝ) ≤ (p : ℝ) ^ ((1 + iwEps ρ) * ((iwN0 ρ l / p : ℕ) : ℝ)) := by
    by_cases hεh : iwEps ρ ≤ 1 / 2
    · exact prime_rpow_le hεpos hεh hN8 hN' hp hpN
    · -- `1/2 < ε_ρ`: apply `prime_rpow_le` with `ε = 1/2` and use monotonicity in the exponent
      have hε2 : 1 / 2 < iwEps ρ := not_le.mp hεh
      have h8le : (2 : ℝ) ^ ((1 + (1 : ℝ) / 2) / (1 / 2)) ≤ (iwN0 ρ l : ℝ) := by
        have he : (1 + (1 : ℝ) / 2) / (1 / 2) = (3 : ℝ) := by norm_num
        rw [he]
        have h23 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
        rw [h23]
        exact_mod_cast hN8
      have hbase : (iwN0 ρ l : ℝ)
          ≤ (p : ℝ) ^ ((1 + (1 : ℝ) / 2) * ((iwN0 ρ l / p : ℕ) : ℝ)) :=
        prime_rpow_le (by norm_num : (0 : ℝ) < 1 / 2) le_rfl hN8 h8le hp hpN
      refine le_trans hbase (Real.rpow_le_rpow_of_exponent_le ?_ ?_)
      · exact_mod_cast hp.one_le
      · have hk : (0 : ℝ) ≤ ((iwN0 ρ l / p : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith [hε2, hk]
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hNpos : (0 : ℝ) < (iwN0 ρ l : ℝ) := by
    exact_mod_cast (show 0 < iwN0 ρ l by rw [iwN0]; exact Nat.succ_pos _)
  -- logarithmic form of `p ^ j ≤ q ≤ 2 ^ l`
  have hstep1 : (j : ℝ) * Real.log (p : ℝ) ≤ (l : ℝ) * Real.log 2 := by
    have h1 : ((p ^ j : ℕ) : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) := by exact_mod_cast le_trans hpj hq
    rw [Nat.cast_pow, Nat.cast_pow] at h1
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow, Real.log_pow] at h2
  have hstep2 : ρ * (l : ℝ) / 2 * Real.log 2 < Real.log (iwN0 ρ l : ℝ) := by
    have h2 := Real.log_lt_log (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hNgt
    rwa [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at h2
  have hstep3 : Real.log (iwN0 ρ l : ℝ) ≤
      (1 + iwEps ρ) * ((iwN0 ρ l / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    have h3 := Real.log_le_log hNpos hNp
    rwa [Real.log_rpow hppos] at h3
  -- the chain `j log p < D_ρ ⌊N_0/p⌋ log p`
  have hchain : (j : ℝ) * Real.log (p : ℝ) <
      ((iwD ρ : ℝ) * ((iwN0 ρ l / p : ℕ) : ℝ)) * Real.log (p : ℝ) := by
    have hρ2 : 0 < 2 / ρ := by positivity
    have heqD : (2 / ρ) * (1 + iwEps ρ) = (iwD ρ : ℝ) := iwD_eq_ratio hρ
    have heq2 : (l : ℝ) * Real.log 2 = (2 / ρ) * (ρ * (l : ℝ) / 2 * Real.log 2) := by
      field_simp
    calc (j : ℝ) * Real.log (p : ℝ) ≤ (l : ℝ) * Real.log 2 := hstep1
      _ = (2 / ρ) * (ρ * (l : ℝ) / 2 * Real.log 2) := heq2
      _ < (2 / ρ) * Real.log (iwN0 ρ l : ℝ) := mul_lt_mul_of_pos_left hstep2 hρ2
      _ ≤ (2 / ρ) * ((1 + iwEps ρ) * ((iwN0 ρ l / p : ℕ) : ℝ) * Real.log (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep3 hρ2.le
      _ = ((iwD ρ : ℝ) * ((iwN0 ρ l / p : ℕ) : ℝ)) * Real.log (p : ℝ) := by
          rw [show (2 / ρ) * ((1 + iwEps ρ) * ((iwN0 ρ l / p : ℕ) : ℝ) * Real.log (p : ℝ))
              = ((2 / ρ) * (1 + iwEps ρ)) * (((iwN0 ρ l / p : ℕ) : ℝ) * Real.log (p : ℝ))
              by ring,
            heqD]
          ring
  have hlt : (j : ℝ) < (iwD ρ : ℝ) * ((iwN0 ρ l / p : ℕ) : ℝ) :=
    lt_of_mul_lt_mul_right hchain hlogp.le
  have hjlt : j < iwD ρ * (iwN0 ρ l / p) := by
    rw [← Nat.cast_mul] at hlt
    exact_mod_cast hlt
  -- Legendre: `⌊N_0/p⌋ ≤ v_p(N_0!)`
  have hwv : iwN0 ρ l / p ≤ (iwN0 ρ l).factorial.factorization p := by
    have hlogN : Nat.log p (iwN0 ρ l) < iwN0 ρ l + 1 := Nat.lt_succ_of_le (Nat.log_le_self _ _)
    rw [Nat.factorization_factorial (b := iwN0 ρ l + 1) hp hlogN]
    have hmem : 1 ∈ Finset.Ico 1 (iwN0 ρ l + 1) :=
      Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hle := Finset.single_le_sum (f := fun i => iwN0 ρ l / p ^ i) (fun i _ => Nat.zero_le _)
      hmem
    simpa using hle
  exact le_trans hjlt.le (Nat.mul_le_mul_left _ hwv)

/-! ## At most `D_ρ` large prime factors -/

/-- **At most `D_ρ` large prime factors** (Appendix A, without the hypothesis `ρ ≤ 1`).
A number `q ≤ 2^l` has at most `D_ρ` distinct prime divisors exceeding `N_0^{(l)}`. -/
private theorem iwPrimeRangeCard_gen {ρ : ℝ} (hρ : 0 < ρ) {l q : ℕ}
    (hl : iwC0 ρ ≤ l) (hq1 : 1 ≤ q) (hq : q ≤ 2 ^ l) :
    ((iwPrimeRange ρ l).filter (fun p => p ∣ q)).card ≤ iwD ρ := by
  set s := (iwPrimeRange ρ l).filter (fun p => p ∣ q) with hs
  have hsp : ∀ p ∈ s, p.Prime := fun p hp =>
    (IwMono.mem_iwPrimeRange_iff.mp (Finset.mem_filter.mp hp).1).2.2
  by_cases hs0 : s.card = 0
  · simp [hs0]
  have hk1 : 1 ≤ s.card := Nat.one_le_iff_ne_zero.mpr hs0
  have hq0 : q ≠ 0 := by omega
  -- the product of the elements of `s` divides `q`
  have hdvd : (∏ p ∈ s, p) ∣ q := by
    have hprod_eq : (∏ p ∈ s, p) = (∏ p ∈ s, p ^ (1:ℕ)) := by simp
    rw [hprod_eq]
    refine (Nat.factorization_le_iff_dvd ?_ (by omega)).mp (fun r => ?_)
    · rw [Finset.prod_ne_zero_iff]
      intro p hp
      exact pow_ne_zero _ (hsp p hp).ne_zero
    · rw [prod_prime_pow_factorization hsp r]
      by_cases hr : r ∈ s
      · rw [if_pos hr]
        have hrq : r ∣ q := (Finset.mem_filter.mp hr).2
        have hrp : r.Prime := hsp r hr
        have hne : q.factorization r ≠ 0 := by
          intro hz
          rcases (Nat.factorization_eq_zero_iff q r).mp hz with h | h | h
          · exact h hrp
          · exact h hrq
          · exact hq0 h
        omega
      · rw [if_neg hr]; exact Nat.zero_le _
  have hprod_le : (∏ p ∈ s, p) ≤ q := Nat.le_of_dvd (by omega) hdvd
  -- `(N_0^{(l)} + 1) ^ s.card ≤ q ≤ 2^l`
  have hN1 : ∀ p ∈ s, iwN0 ρ l + 1 ≤ p := fun p hp =>
    Nat.succ_le_of_lt (IwMono.mem_iwPrimeRange_iff.mp (Finset.mem_filter.mp hp).1).1
  have hpow_le : (iwN0 ρ l + 1) ^ s.card ≤ q := by
    calc (iwN0 ρ l + 1) ^ s.card = ∏ _p ∈ s, (iwN0 ρ l + 1) := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ s, p := Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) hN1
      _ ≤ q := hprod_le
  -- logarithmic chain
  have hN1gt : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) < ((iwN0 ρ l + 1 : ℕ) : ℝ) := by
    have h := IwCont.iwN0_gt ρ l
    push_cast
    linarith
  have hP : (0:ℝ) < ((iwN0 ρ l + 1 : ℕ) : ℝ) := by positivity
  have hstep1 : (s.card : ℝ) * (ρ * (l : ℝ) / 2 * Real.log 2)
      < (s.card : ℝ) * Real.log ((iwN0 ρ l + 1 : ℕ) : ℝ) := by
    have h2 : ρ * (l : ℝ) / 2 * Real.log 2 < Real.log ((iwN0 ρ l + 1 : ℕ) : ℝ) := by
      have h3 := Real.log_lt_log (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _) hN1gt
      rwa [Real.log_rpow (by norm_num : (0:ℝ) < 2)] at h3
    exact mul_lt_mul_of_pos_left h2 (by exact_mod_cast (by omega : 0 < s.card))
  have hstep2 : (s.card : ℝ) * Real.log ((iwN0 ρ l + 1 : ℕ) : ℝ) ≤ (l : ℝ) * Real.log 2 := by
    have h1 : (((iwN0 ρ l + 1) ^ s.card : ℕ) : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) := by
      exact_mod_cast le_trans hpow_le hq
    rw [Nat.cast_pow, Nat.cast_pow] at h1
    have h2 := Real.log_le_log (pow_pos hP _) h1
    rwa [Real.log_pow, Real.log_pow] at h2
  have hmain : (s.card : ℝ) * (ρ * (l : ℝ) / 2) < (l : ℝ) := by
    have h4 : (s.card : ℝ) * (ρ * (l : ℝ) / 2) * Real.log 2 < (l : ℝ) * Real.log 2 := by
      have := lt_of_lt_of_le hstep1 hstep2
      nlinarith [this]
    exact (mul_lt_mul_iff_of_pos_right (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp h4
  have hkey : ρ * (s.card : ℝ) / 2 < 1 := by
    have hlpos : 0 < (l : ℝ) := by
      have h1 : (100:ℕ) ≤ iwC0 ρ := by rw [iwC0]; omega
      exact_mod_cast (by omega : 0 < l)
    nlinarith [hmain, hlpos]
  have hlt : (s.card : ℝ) < (iwD ρ : ℝ) := by
    have h3' : (s.card : ℝ) < 2 / ρ := by rw [lt_div_iff₀ hρ]; nlinarith [hkey]
    have := iwD_gt ρ; linarith
  exact Nat.le_of_lt (by exact_mod_cast hlt)

/-! ## The two halves of the representation at level `l` -/

/-- **The small-prime part of `q` divides `Q_0^{(l)}`** (without the hypothesis `ρ ≤ 1`). -/
private theorem iwLow_dvd_iwQ0_gen {ρ : ℝ} (hρ : 0 < ρ) {l q : ℕ}
    (hl : iwC0 ρ ≤ l) (hq1 : 1 ≤ q) (hq : q ≤ 2 ^ l) :
    IwMono.iwLow (iwN0 ρ l) q ∣ iwQ0 ρ l := by
  refine (Nat.factorization_le_iff_dvd (IwMono.iwLow_ne_zero _ _) (iwQ0_ne_zero ρ l)).mp (fun p => ?_)
  rw [IwMono.iwLow_factorization, IwMono.iwQ0_factorization]
  by_cases hc : p ∈ q.factorization.support.filter (fun p => p ≤ iwN0 ρ l)
  · rw [if_pos hc]
    obtain ⟨hpsupp, hple⟩ := Finset.mem_filter.mp hc
    have hne : q.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hpsupp
    have hpprime : p.Prime := by
      by_contra hp'
      exact hne ((Nat.factorization_eq_zero_iff q p).mpr (Or.inl hp'))
    have hle : p ^ q.factorization p ≤ q := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd q p)
    exact iwC0SmallPrimeExp_gen hρ hl hq hpprime hple hle
  · rw [if_neg hc]; exact Nat.zero_le _

/-- **The large-prime part of `q` lies in `W_{≤l}`** (without the hypothesis `ρ ≤ 1`). -/
private theorem iwHigh_mem_iwW_gen {ρ : ℝ} (hρ : 0 < ρ) {l q : ℕ}
    (hl : iwC0 ρ ≤ l) (hq1 : 1 ≤ q) (hq : q ≤ 2 ^ l) :
    IwMono.iwHigh (iwN0 ρ l) q ∈ iwW ρ l := by
  have hq0 : q ≠ 0 := by omega
  refine mem_iwW.mpr ⟨?_, ?_⟩
  · refine (Nat.factorization_le_iff_dvd (IwMono.iwHigh_ne_zero _ _) (iwProd_ne_zero ρ l)).mp
      (fun p => ?_)
    rw [IwMono.iwHigh_factorization, IwMono.iwProd_factorization]
    by_cases hc : p ∈ q.factorization.support.filter (fun p => iwN0 ρ l < p)
    · rw [if_pos hc]
      obtain ⟨hpsupp, hplt⟩ := Finset.mem_filter.mp hc
      have hne : q.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hpsupp
      have hpprime : p.Prime := by
        by_contra hp'
        exact hne ((Nat.factorization_eq_zero_iff q p).mpr (Or.inl hp'))
      have hpq : p ∣ q := by
        by_contra hp'
        exact hne ((Nat.factorization_eq_zero_iff q p).mpr (Or.inr (Or.inl hp')))
      have hple : p ≤ 2 ^ l := Nat.le_trans (Nat.le_of_dvd (by omega) hpq) hq
      rw [if_pos (IwMono.mem_iwPrimeRange_iff.mpr ⟨hplt, hple, hpprime⟩)]
      exact IwCont.factorization_le_iwD hρ hl hq1 hq hpprime hplt
    · rw [if_neg hc]; exact Nat.zero_le _
  · rw [IwMono.iwHigh_support, IwCont.support_high_eq hq0 hq]
    exact iwPrimeRangeCard_gen hρ hl hq1 hq

/-- **Appendix A, inclusion `[2^l] ⊆ P_{≤l}`** for every `ρ > 0`: for `l ≥ C⁰_ρ`, every
denominator `1 ≤ q ≤ 2^l` belongs to the concrete Ionescu–Wainger set `iwPconcrete ρ l`. -/
private theorem iwPconcrete_contains_range_gen {ρ : ℝ} (hρ : 0 < ρ) {l q : ℕ}
    (hl : iwC0 ρ ≤ l) (hq1 : 1 ≤ q) (hq2 : q ≤ 2 ^ l) : q ∈ iwPconcrete ρ l := by
  have hq0 : q ≠ 0 := by omega
  refine mem_iwPconcrete.mpr
    ⟨IwMono.iwLow (iwN0 ρ l) q,
     Nat.mem_divisors.mpr ⟨iwLow_dvd_iwQ0_gen hρ hl hq1 hq2, iwQ0_ne_zero ρ l⟩,
     IwMono.iwHigh (iwN0 ρ l) q, iwHigh_mem_iwW_gen hρ hl hq1 hq2, ?_⟩
  exact (IwMono.iwLow_mul_iwHigh (m := iwN0 ρ l) (w := q) hq0).symm

/-! ## Monotonicity of the denominator sets and of the frequency sets -/

private theorem iwP_succ_all {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) : iwP ρ l ⊆ iwP ρ (l + 1) := by
  intro q hq
  rw [mem_iwP] at hq ⊢
  rcases hq with ⟨hl, h1, h2⟩ | ⟨hl, hq⟩
  · by_cases h : l + 1 ≤ iwC0 ρ
    · exact Or.inl ⟨h, h1, le_trans h2 (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ l))⟩
    · refine Or.inr ⟨not_le.mp h, iwPconcrete_contains_range_gen hρ ?_ h1 ?_⟩
      · omega
      · exact le_trans h2 (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ l))
  · exact Or.inr ⟨by omega, iwPconcrete_mono (Nat.le_succ l) hq⟩

/-- The Ionescu–Wainger denominator sets are non-decreasing in `l`, for every `ρ > 0`. -/
private theorem iwP_mono_all {ρ : ℝ} (hρ : 0 < ρ) : Monotone (iwP ρ) :=
  monotone_nat_of_le_succ (iwP_succ_all hρ)

/-! ## Public statements of the generalised Appendix A inputs -/

/-- **Appendix A, `[2^l] ⊆ P_{≤l}`, for every `ρ > 0`** (the generalisation of
`Work.Analysis.IonescuWainger.iwPconcrete_contains_range`, which assumes `ρ ≤ 1`). -/
theorem iwPconcrete_contains_range_of_pos {ρ : ℝ} (hρ : 0 < ρ) {l q : ℕ}
    (hl : iwC0 ρ ≤ l) (hq1 : 1 ≤ q) (hq2 : q ≤ 2 ^ l) : q ∈ iwPconcrete ρ l :=
  iwPconcrete_contains_range_gen hρ hl hq1 hq2

/-- The Ionescu–Wainger denominator sets `P_{≤l}` are non-decreasing in `l`, for every `ρ > 0`
(the generalisation of `Work.Analysis.IonescuWainger.iwP_mono`, which assumes `ρ ≤ 1`). -/
theorem iwP_mono_of_pos {ρ : ℝ} (hρ : 0 < ρ) : Monotone (iwP ρ) := iwP_mono_all hρ

/-- **`(ℚ/ℤ)_{≤l}` is non-decreasing in `l`, for every `ρ > 0`.**  This removes the hypothesis
`ρ ≤ 1` from `Work.Analysis.IonescuWainger.iwArithFreqs_mono`. -/
theorem iwArithFreqs_mono_all {ρ : ℝ} (hρ : 0 < ρ) :
    Monotone (Work.Analysis.IonescuWainger.iwArithFreqs ρ) := by
  intro l l' hll' α hα
  rw [mem_iwArithFreqs] at hα ⊢
  obtain ⟨q, hq, hqα⟩ := hα
  exact ⟨q, iwP_mono_all hρ hll' hq, hqα⟩

end Work.KMTPlan.A6.LowModApproxBoundedH
