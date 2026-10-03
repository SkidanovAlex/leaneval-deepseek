import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S40

set_option maxHeartbeats 30000000

namespace Work.FIChain

open Finset Filter
open Submission.ASP
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `(R′)` for `ã` at *every* scale `m ≤ x`

`Submission.ASP.FI_RemainderSum_atil_le` proves the `(R′)`-estimate

  `RemainderSum r̃_full (Rcut x) m ≤ Ã(x)(log x)^{-3}`

only in the range `Rcut x ≤ m ≤ x` (which is what the companion's sieve consumes).  The present
lemma removes that restriction: for `m < Rcut x = ⌊x^{11/16}⌋` we bound `RemainderSum` crudely,
using the exact identity `r̃_full(d,m) = Ã_d(m) − g̃(d)Ã(m)` of `ASP.S9g` together with the
`τ^{20/3}`-weighted mean-value `(2.1)` (`ASP.S39.sum_tau_pow_AtilAd_le`) at the small scale `m`,
resp. by a constant times a power of `log x` for the *fixed* finitely many `m < M₀`.

Everything is dominated by the `x^{3/4}`-growth of `Ã(x)`:  the crude bound is
`≪ x^{33/64}(log x)^{O(1)}`, and `x^{33/64}(log x)^{O(1)} ≤ c·x^{3/4}(log x)^{-3}` for `x ≥ X₀`.
-/

/-! ## 1. Elementary facts about the remainder -/

/-- `Ã_d(m) = 0` when `d > m`: no `1 ≤ n ≤ m` is divisible by `d`. -/
lemma AtilAd_eq_zero_of_lt {d m : ℕ} (h : m < d) : AtilAd FIa d m = 0 := by
  rw [AtilAd, Ad, Nat.floor_natCast]
  refine Finset.sum_eq_zero (fun n hn => ?_)
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnm⟩, hdn⟩ := hn
  have hle : d ≤ n := Nat.le_of_dvd (by omega) hdn
  omega

/-- `Ã_d(m) ≤ Ã(m)`: a sub-sum of a sum of nonnegative terms. -/
lemma AtilAd_le_Acount (d m : ℕ) : AtilAd FIa d m ≤ Acount (atil FIa) (m : ℝ) := by
  rw [AtilAd, Ad, Acount, Nat.floor_natCast]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => atil_nonneg FIa_nonneg i)

/-- `Ã(m) ≤ A(m) = Aseq m − 1`. -/
lemma Acount_atil_le_Aseq (m : ℕ) : Acount (atil FIa) (m : ℝ) ≤ (Submission.Aseq m : ℝ) := by
  have h1 := Acount_atil_le FIa FIa_nonneg (m : ℝ)
  rw [FI_Acount_eq m] at h1
  linarith

lemma AtilAd_le_Aseq (d m : ℕ) : AtilAd FIa d m ≤ (Submission.Aseq m : ℝ) :=
  le_trans (AtilAd_le_Acount d m) (Acount_atil_le_Aseq m)

/-- The exact identity of `ASP.S9g`: `r̃_full(d,m) = Ã_d(m) − g̃(d)·Ã(m)`. -/
lemma rtildeFull_eq (d m : ℕ) :
    rtildeFull FIr FIg FIgtil FIa d m
      = AtilAd FIa d m - FIgtil d * Acount (atil FIa) (m : ℝ) := by
  have h := approx_atil FIa FIg FIr FIgtil (m : ℝ) (FI_approx (m : ℝ)) d m
  have h' : AtilAd FIa d m
      = FIgtil d * Acount (atil FIa) (m : ℝ) + rtildeFull FIr FIg FIgtil FIa d m := h
  linarith

/-- Pointwise bound of the honest remainder by the two nonnegative pieces. -/
lemma abs_rtildeFull_le' (d m : ℕ) :
    |rtildeFull FIr FIg FIgtil FIa d m|
      ≤ AtilAd FIa d m + FIgtil d * Acount (atil FIa) (m : ℝ) := by
  rw [rtildeFull_eq]
  have h1 : (0 : ℝ) ≤ AtilAd FIa d m := AtilAd_nonneg FIa FIa_nonneg d m
  have h2 : (0 : ℝ) ≤ FIgtil d * Acount (atil FIa) (m : ℝ) :=
    mul_nonneg (FIgtil_nonneg d)
      (Finset.sum_nonneg (fun n _ => atil_nonneg FIa_nonneg n))
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- `1 ≤ τ(d)` for `d ≥ 1`. -/
lemma one_le_tau_card {d : ℕ} (hd : 1 ≤ d) : (1 : ℝ) ≤ ((d.divisors.card : ℕ) : ℝ) := by
  have : 1 ≤ d.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  exact_mod_cast this

/-- `τ(d)^5 ≤ τ(d)^{20/3}` for `d ≥ 1`. -/
lemma tau_five_le_tau_rpow {d : ℕ} (hd : 1 ≤ d) :
    ((d.divisors.card : ℝ)) ^ (5 : ℕ) ≤ ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) := by
  have h1 : (1:ℝ) ≤ ((d.divisors.card : ℕ) : ℝ) := one_le_tau_card hd
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)

/-! ## 2. The two weighted sums -/

/-- The `τ⁵`-weighted `Ã_d(m)`-sum over `d ≤ Rcut x`, bounded with the `(2.1)`-input at scale
`m` (which is legitimate because the terms with `m < d ≤ Rcut x` vanish). -/
lemma termA_le_large {C B X1 : ℝ} {x m : ℕ}
    (h21 : ∀ y : ℕ, X1 ≤ (y : ℝ) → ∀ n : ℕ, 2 ≤ n → n ≤ y →
      ∀ D : ℕ, D ≤ n →
        (∑ d ∈ Finset.Icc 1 D,
            ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d n)
          ≤ C * (Submission.Aseq y : ℝ) * (Real.log (y : ℝ)) ^ B)
    (hmX : X1 ≤ (m : ℝ)) (hm2 : 2 ≤ m) (hmD : m ≤ Submission.Rcut x) :
    (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ (5 : ℕ) * AtilAd FIa d m)
      ≤ C * (Submission.Aseq m : ℝ) * (Real.log (m : ℝ)) ^ B := by
  have h1 : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ (5 : ℕ) * AtilAd FIa d m)
      ≤ ∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
          ((d.divisors.card : ℝ)) ^ (5 : ℕ) * AtilAd FIa d m := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun d : ℕ => Squarefree d) (Finset.Icc 1 (Submission.Rcut x))) ?_
    intro d _ _
    exact mul_nonneg (by positivity) (AtilAd_nonneg FIa FIa_nonneg d m)
  have h2 : (∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
          ((d.divisors.card : ℝ)) ^ (5 : ℕ) * AtilAd FIa d m)
      ≤ ∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
          ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d m :=
    Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_right
      (tau_five_le_tau_rpow (Finset.mem_Icc.mp hd).1) (AtilAd_nonneg FIa FIa_nonneg d m))
  have hstep2 : (∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
          ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d m)
      = ∑ d ∈ Finset.Icc 1 (min (Submission.Rcut x) m),
          ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * AtilAd FIa d m := by
    rw [eq_comm]
    refine Finset.sum_subset ?_ ?_
    · intro d hd
      rw [Finset.mem_Icc] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 (min_le_left _ _)⟩
    · intro d hdD hdnot
      rw [Finset.mem_Icc] at hdD
      have hlt : min (Submission.Rcut x) m < d := by
        by_contra hcon
        rw [not_lt] at hcon
        exact hdnot (Finset.mem_Icc.mpr ⟨hdD.1, hcon⟩)
      have hmd : m < d := by omega
      rw [AtilAd_eq_zero_of_lt hmd, mul_zero]
  have hstep3 := h21 m hmX m hm2 le_rfl (min (Submission.Rcut x) m) (min_le_right _ _)
  exact le_trans (le_trans h1 h2) (le_trans (le_of_eq hstep2) hstep3)

/-- The `τ⁵`-weighted `g̃`-sum over `d ≤ Rcut x`, bounded with the `(2.2)`-input. -/
lemma termB_le {C K : ℝ} {x : ℕ}
    (h22 : ∀ y : ℕ, 2 ≤ y →
      (∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * FIgtil d) ≤ C * (Real.log (y : ℝ)) ^ K)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hD1 : 1 ≤ Submission.Rcut x) (hDle : Submission.Rcut x ≤ x)
    (hD2 : 2 ≤ Submission.Rcut x) :
    (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ (5 : ℕ) * FIgtil d)
      ≤ C * (Real.log (x : ℝ)) ^ K := by
  have hlogRnn : (0 : ℝ) ≤ Real.log ((Submission.Rcut x : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hD1)
  have hlogRle : Real.log ((Submission.Rcut x : ℕ) : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hDle)
  refine le_trans ?_ (le_trans (h22 (Submission.Rcut x) hD2) ?_)
  · refine Finset.sum_le_sum (fun d hd => ?_)
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    exact mul_le_mul_of_nonneg_right (tau_five_le_tau_rpow hd1) (FIgtil_nonneg d)
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlogRnn hlogRle hK) hC

/-! ## 3. Numerical comparison lemmas -/

/-- `(log m)^B ≤ max 1 ((log 2)^B) · (log x)^{⌈B⌉_+}` for `3 ≤ m ≤ x`. -/
lemma logpow_le_const_mul {B : ℝ} {m x : ℝ} (hm : 3 ≤ m) (hmx : m ≤ x) :
    Real.log m ^ B ≤ max 1 (Real.log 2 ^ B) * Real.log x ^ (⌈max B 0⌉₊ : ℕ) := by
  have hlogm1 : 1 ≤ Real.log m := by
    have h3 : Real.log 3 ≤ Real.log m := Real.log_le_log (by norm_num) hm
    have h1 : 1 ≤ Real.log 3 := one_le_log_three
    linarith
  have hlogx1 : 1 ≤ Real.log x := le_trans hlogm1 (Real.log_le_log (by linarith) hmx)
  by_cases hB : 0 ≤ B
  · have h1 : Real.log m ^ B ≤ Real.log x ^ B :=
      Real.rpow_le_rpow (by linarith) (Real.log_le_log (by linarith) hmx) hB
    have h2 : Real.log x ^ B ≤ Real.log x ^ ((⌈max B 0⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlogx1
        (le_trans (le_max_left B 0) (Nat.le_ceil _))
    rw [Real.rpow_natCast] at h2
    have h3 : (1:ℝ) ≤ max 1 (Real.log 2 ^ B) := le_max_left _ _
    calc Real.log m ^ B ≤ Real.log x ^ B := h1
      _ ≤ Real.log x ^ (⌈max B 0⌉₊ : ℕ) := h2
      _ = 1 * Real.log x ^ (⌈max B 0⌉₊ : ℕ) := (one_mul _).symm
      _ ≤ max 1 (Real.log 2 ^ B) * Real.log x ^ (⌈max B 0⌉₊ : ℕ) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
  · push_neg at hB
    have h1 : Real.log m ^ B ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hlogm1 (le_of_lt hB)
    have h3 : (1:ℝ) ≤ max 1 (Real.log 2 ^ B) := le_max_left _ _
    have h4 : (1:ℝ) ≤ Real.log x ^ (⌈max B 0⌉₊ : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.one_le_rpow hlogx1 (Nat.cast_nonneg _)
    have h2 : (1:ℝ) ≤ max 1 (Real.log 2 ^ B) * Real.log x ^ (⌈max B 0⌉₊ : ℕ) := by
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ _ := mul_le_mul h3 h4 (by norm_num) (le_trans zero_le_one h3)
    linarith

/-- `m^{3/4} ≤ x^{33/64}` for `m < ⌊x^{11/16}⌋`. -/
lemma rpow_three_quarters_le {m x : ℕ} (hmD : m < Submission.Rcut x) :
    (m : ℝ) ^ ((3:ℝ)/4) ≤ (x : ℝ) ^ ((33:ℝ)/64) := by
  have hm_lt : (m : ℝ) < (x : ℝ) ^ ((11:ℝ)/16) := by
    have h1 : ((m:ℝ)) < ((Submission.Rcut x : ℕ) : ℝ) := by exact_mod_cast hmD
    have h2 : ((Submission.Rcut x : ℕ) : ℝ) ≤ (x:ℝ) ^ ((11:ℝ)/16) := Submission.Rcut_le_rpow x
    linarith
  have h1 : (m:ℝ) ^ ((3:ℝ)/4) ≤ ((x:ℝ) ^ ((11:ℝ)/16)) ^ ((3:ℝ)/4) :=
    Real.rpow_le_rpow (by positivity) (le_of_lt hm_lt) (by norm_num)
  have h2 : ((x:ℝ) ^ ((11:ℝ)/16)) ^ ((3:ℝ)/4) = (x:ℝ) ^ ((33:ℝ)/64) := by
    rw [← Real.rpow_mul (by positivity)]
    norm_num
  linarith [h1, h2.le]

/-- The small-`x` comparison: from `(K/c)·(log x)^{N+3} ≤ Y` conclude
`K·(log x)^N ≤ c·Y·(log x)^{-3}`. -/
lemma logpow_le_of_threshold {K c L Y : ℝ} {N : ℕ}
    (hL : 1 ≤ L) (hc : 0 < c)
    (h : (K / c) * L ^ (N + 3) ≤ Y) :
    K * L ^ N ≤ c * Y * L ^ (-(3:ℝ)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpos3 : 0 < L ^ (3:ℝ) := Real.rpow_pos_of_pos hL0 3
  have h1 : K * L ^ (N + 3) ≤ c * Y := by
    have h' := mul_le_mul_of_nonneg_right h hc.le
    rw [show (K / c) * L ^ (N + 3) * c = K * L ^ (N + 3) by field_simp,
        show Y * c = c * Y by ring] at h'
    exact h'
  have hN : L ^ (N + 3) = L ^ N * L ^ (3:ℝ) := by
    rw [← Real.rpow_natCast]
    rw [show ((N + 3 : ℕ) : ℝ) = (N:ℝ) + 3 by push_cast; ring]
    rw [Real.rpow_add hL0, Real.rpow_natCast]
  rw [hN] at h1
  rw [Real.rpow_neg (le_of_lt hL0), inv_eq_one_div, mul_one_div, le_div_iff₀ hpos3]
  simpa [mul_assoc] using h1

/-! ## 4. The theorem -/

theorem remainder_all :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ m : ℕ, m ≤ x →
      Submission.ASP.RemainderSum (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
          Submission.ASP.FIgtil Submission.ASP.FIa) (Submission.Rcut x) m
        ≤ Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℝ)) := by
  obtain ⟨X40, h40⟩ := Submission.ASP.FI_RemainderSum_atil_le
  obtain ⟨C1, B1, X1, hC1, h21raw⟩ := Submission.ASP.sum_tau_pow_AtilAd_le
  obtain ⟨C2, K2, hC2, hK2, h22raw⟩ := Submission.ASP.sum_sqfree_tau_pow_FIgtil_le
  obtain ⟨CF, hCF, hCFb⟩ := Submission.Aseq_le_const_mul_rpow
  obtain ⟨cA, hcA, XA, hAc⟩ := Submission.exists_const_mul_rpow_le_Aseq
  obtain ⟨XG, hG⟩ := Submission.ASP.FI_Aseq_le_const_mul_Atil
  have hGp : (0 : ℝ) < Submission.ASP.Gprod Submission.ASP.FIg := Submission.ASP.Gprod_FIg_pos
  -- the cutoff for the "crude" range
  set M0 : ℕ := max ⌈X1⌉₊ 3 with hM0def
  have hX1le : X1 ≤ (M0 : ℝ) := by
    have h1 : X1 ≤ ((⌈X1⌉₊ : ℕ) : ℝ) := Nat.le_ceil X1
    have h2 : (⌈X1⌉₊ : ℕ) ≤ M0 := le_max_left _ _
    exact le_trans h1 (by exact_mod_cast h2)
  have hM0_3 : 3 ≤ M0 := le_max_right _ _
  -- the accumulated constants
  set Ctc : ℝ := max 1 ((Real.log 2) ^ B1) with hCtcdef
  have hCtc1 : (1 : ℝ) ≤ Ctc := le_max_left _ _
  have hCtc0 : (0 : ℝ) < Ctc := lt_of_lt_of_le zero_lt_one hCtc1
  set N1 : ℕ := ⌈max B1 0⌉₊ with hN1def
  set Kc : ℝ := C1 * CF * Ctc + CF * C2 with hKcdef
  have hKc0 : 0 ≤ Kc := by rw [hKcdef]; positivity
  set c' : ℝ := cA / (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) with hc'def
  have hc'0 : 0 < c' := by rw [hc'def]; positivity
  set KA : ℝ := ∑ d ∈ Finset.Icc 1 M0, ((d.divisors.card : ℝ)) ^ (5 : ℕ) with hKAdef
  have hKA0 : 0 ≤ KA := by
    rw [hKAdef]
    exact Finset.sum_nonneg (fun d _ => by positivity)
  set Ksm : ℝ := KA * (Submission.Aseq M0 : ℝ) + (Submission.Aseq M0 : ℝ) * C2 with hKsmdef
  have hKsm0 : 0 ≤ Ksm := by
    rw [hKsmdef]
    exact add_nonneg (mul_nonneg hKA0 (by positivity))
      (mul_nonneg (by positivity) (le_of_lt hC2))
  obtain ⟨Xt1, _hXt1_1, ht1⟩ := Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold
    (K := Kc / c') (div_nonneg hKc0 (le_of_lt hc'0)) (n := N1 + ⌈K2⌉₊ + 3) (r := 15/64)
    (by norm_num)
  obtain ⟨Xt2, _hXt2_1, ht2⟩ := Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold
    (K := Ksm / c') (div_nonneg hKsm0 (le_of_lt hc'0)) (n := ⌈K2⌉₊ + 3) (r := 15/64)
    (by norm_num)
  refine ⟨max (max (max X40 ⌈Xt1⌉₊) (max ⌈Xt2⌉₊ (max XA XG))) (max M0 64), ?_⟩
  intro x hx m hmx
  have hx40 : X40 ≤ x := by omega
  have hxt1 : ⌈Xt1⌉₊ ≤ x := by omega
  have hxt2 : ⌈Xt2⌉₊ ≤ x := by omega
  have hxXA : XA ≤ x := by omega
  have hxXG : XG ≤ x := by omega
  have hxM0 : M0 ≤ x := by omega
  have hx64 : 64 ≤ x := by omega
  have hx5 : 5 ≤ x := by omega
  have hx3 : 3 ≤ x := by omega
  have hx1N : 1 ≤ x := by omega
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hlogx1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
    have he : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlogx0 : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hlogx1
  have hlogxnn : (0 : ℝ) ≤ Real.log (x : ℝ) := le_of_lt hlogx0
  have hD2 : 2 ≤ Submission.Rcut x := Submission.two_le_Rcut hx5
  have hD1 : 1 ≤ Submission.Rcut x := le_trans (by norm_num) hD2
  have hDle : Submission.Rcut x ≤ x := Submission.Rcut_le_self x
  -- `c'·x^{3/4} ≤ Ã(x)`
  have hcx : c' * (x : ℝ) ^ ((3:ℝ)/4) ≤ Acount (atil FIa) (x : ℝ) := by
    have h1 : cA * (x : ℝ) ^ ((3:ℝ)/4) ≤ (Submission.Aseq x : ℝ) := hAc x hxXA
    have h2 : (Submission.Aseq x : ℝ) - 1
        ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg) * Acount (atil FIa) (x : ℝ) := by
      have h := hG x hxXG
      rw [FI_Acount_eq x] at h
      linarith
    have h3 : (1 : ℝ) ≤ Acount (atil FIa) (x : ℝ) := one_le_Acount_atil x hx1N
    have hKpos : (0 : ℝ) < 2 / Submission.ASP.Gprod Submission.ASP.FIg + 1 := by positivity
    have h4 : (Submission.Aseq x : ℝ)
        ≤ Acount (atil FIa) (x : ℝ) * (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) := by
      have h5 : (2 / Submission.ASP.Gprod Submission.ASP.FIg) * Acount (atil FIa) (x : ℝ) + 1
          ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) * Acount (atil FIa) (x : ℝ) := by
        have h6 : (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) * Acount (atil FIa) (x : ℝ)
            = (2 / Submission.ASP.Gprod Submission.ASP.FIg) * Acount (atil FIa) (x : ℝ)
              + Acount (atil FIa) (x : ℝ) := by ring
        rw [h6]
        linarith
      have h7 : Acount (atil FIa) (x : ℝ) * (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1)
          = (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) * Acount (atil FIa) (x : ℝ) := by
        ring
      rw [h7]
      linarith
    rw [hc'def, div_mul_eq_mul_div, div_le_iff₀ hKpos]
    linarith
  by_cases hDm : Submission.Rcut x ≤ m
  · exact h40 x hx40 m hDm hmx
  · push_neg at hDm
    -- the decomposition of `RemainderSum` into the `Ã_d`-part and the `g̃`-part
    have hdecomp :
        Submission.ASP.RemainderSum (rtildeFull FIr FIg FIgtil FIa) (Submission.Rcut x) m
          ≤ (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
                ((d.divisors.card : ℝ)) ^ (5:ℕ) * AtilAd FIa d m)
            + Acount (atil FIa) (m : ℝ) *
              (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
                ((d.divisors.card : ℝ)) ^ (5:ℕ) * FIgtil d) := by
      rw [Submission.ASP.RemainderSum]
      have h2 : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
            ((d.divisors.card : ℝ)) ^ (5:ℕ) * (FIgtil d * Acount (atil FIa) (m:ℝ)))
          = Acount (atil FIa) (m:ℝ)
            * ∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
                ((d.divisors.card : ℝ)) ^ (5:ℕ) * FIgtil d := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun d _ => by ring)
      calc ∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
              ((d.divisors.card : ℝ)) ^ (5:ℕ) * |rtildeFull FIr FIg FIgtil FIa d m|
          ≤ ∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
              ((d.divisors.card : ℝ)) ^ (5:ℕ)
                * (AtilAd FIa d m + FIgtil d * Acount (atil FIa) (m:ℝ)) :=
            Finset.sum_le_sum (fun d _ =>
              mul_le_mul_of_nonneg_left (abs_rtildeFull_le' d m) (by positivity))
        _ = (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
                ((d.divisors.card : ℝ)) ^ (5:ℕ) * AtilAd FIa d m)
              + (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
                ((d.divisors.card : ℝ)) ^ (5:ℕ) * (FIgtil d * Acount (atil FIa) (m:ℝ))) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun d _ => by ring)
        _ = (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
                ((d.divisors.card : ℝ)) ^ (5:ℕ) * AtilAd FIa d m)
              + Acount (atil FIa) (m : ℝ) *
                (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
                  ((d.divisors.card : ℝ)) ^ (5:ℕ) * FIgtil d) := by rw [h2]
    have hSBle : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ (5:ℕ) * FIgtil d) ≤ C2 * (Real.log (x:ℝ)) ^ K2 :=
      termB_le h22raw (le_of_lt hC2) hK2 hD1 hDle hD2
    have hSB0 : (0 : ℝ) ≤ ∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ (5:ℕ) * FIgtil d :=
      Finset.sum_nonneg (fun d _ => mul_nonneg (by positivity) (FIgtil_nonneg d))
    by_cases hsmall : m < M0
    · -- the finitely many small scales: everything is bounded by a constant times a power of log
      have hAmono : (Submission.Aseq m : ℝ) ≤ (Submission.Aseq M0 : ℝ) := by
        exact_mod_cast Submission.Aseq_mono (le_of_lt hsmall)
      have hA0 : (0:ℝ) ≤ (Submission.Aseq M0 : ℝ) := by positivity
      have hAsmall : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
            ((d.divisors.card : ℝ)) ^ (5:ℕ) * AtilAd FIa d m) ≤ KA * (Submission.Aseq M0 : ℝ) := by
        have hrw : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
              ((d.divisors.card : ℝ)) ^ (5:ℕ) * AtilAd FIa d m)
            = ∑ d ∈ ((Finset.Icc 1 (Submission.Rcut x)).filter Squarefree).filter
                (fun d => d ≤ M0),
                ((d.divisors.card : ℝ)) ^ (5:ℕ) * AtilAd FIa d m := by
          rw [eq_comm]
          refine Finset.sum_subset
            (Finset.filter_subset (fun d : ℕ => d ≤ M0)
              ((Finset.Icc 1 (Submission.Rcut x)).filter Squarefree)) ?_
          intro d hds hdnot
          have hgt : M0 < d := by
            by_contra hcon
            rw [not_lt] at hcon
            exact hdnot (Finset.mem_filter.mpr ⟨hds, hcon⟩)
          have hmd : m < d := lt_trans hsmall hgt
          rw [AtilAd_eq_zero_of_lt hmd, mul_zero]
        rw [hrw]
        calc ∑ d ∈ ((Finset.Icc 1 (Submission.Rcut x)).filter Squarefree).filter
                (fun d => d ≤ M0), ((d.divisors.card : ℝ)) ^ (5:ℕ) * AtilAd FIa d m
            ≤ ∑ d ∈ Finset.Icc 1 M0,
                ((d.divisors.card : ℝ)) ^ (5:ℕ) * AtilAd FIa d m := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro d hd
                rw [Finset.mem_filter] at hd
                obtain ⟨hdf, hdle⟩ := hd
                rw [Finset.mem_filter, Finset.mem_Icc] at hdf
                exact Finset.mem_Icc.mpr ⟨hdf.1.1, hdle⟩
              · intro d _ _
                exact mul_nonneg (by positivity) (AtilAd_nonneg FIa FIa_nonneg d m)
          _ ≤ ∑ d ∈ Finset.Icc 1 M0,
                ((d.divisors.card : ℝ)) ^ (5:ℕ) * (Submission.Aseq M0 : ℝ) :=
              Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left
                (le_trans (AtilAd_le_Aseq d m) hAmono) (by positivity))
          _ = KA * (Submission.Aseq M0 : ℝ) := by
              rw [hKAdef, Finset.sum_mul]
      have hLq0 : (0:ℝ) ≤ (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) := by positivity
      have hLq1 : (1:ℝ) ≤ (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) := one_le_pow₀ hlogx1
      have htot : Submission.ASP.RemainderSum (rtildeFull FIr FIg FIgtil FIa) (Submission.Rcut x) m
          ≤ Ksm * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) := by
        have h4 : Acount (atil FIa) (m:ℝ)
              * (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
                  ((d.divisors.card : ℝ)) ^ (5:ℕ) * FIgtil d)
            ≤ (Submission.Aseq M0 : ℝ) * (C2 * (Real.log (x:ℝ))^K2) :=
          mul_le_mul (le_trans (Acount_atil_le_Aseq m) hAmono) hSBle hSB0 hA0
        have h5 : (Submission.Aseq M0 : ℝ) * (C2 * (Real.log (x:ℝ))^K2)
            ≤ (Submission.Aseq M0 : ℝ) * C2 * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) := by
          have h6 : (Real.log (x:ℝ)) ^ K2 ≤ (Real.log (x:ℝ)) ^ ((⌈K2⌉₊ : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hlogx1 (Nat.le_ceil K2)
          rw [Real.rpow_natCast] at h6
          calc (Submission.Aseq M0 : ℝ) * (C2 * (Real.log (x:ℝ))^K2)
              ≤ (Submission.Aseq M0 : ℝ) * (C2 * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 (le_of_lt hC2)) hA0
            _ = (Submission.Aseq M0 : ℝ) * C2 * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) := by ring
        have h7 : KA * (Submission.Aseq M0 : ℝ)
              + (Submission.Aseq M0 : ℝ) * C2 * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ)
            ≤ (KA * (Submission.Aseq M0 : ℝ) + (Submission.Aseq M0 : ℝ) * C2)
              * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) := by
          have h8 : KA * (Submission.Aseq M0 : ℝ)
              ≤ KA * (Submission.Aseq M0 : ℝ) * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) :=
            le_mul_of_one_le_right (mul_nonneg hKA0 (by positivity)) hLq1
          have h9 : (Submission.Aseq M0 : ℝ) * C2
              ≤ (Submission.Aseq M0 : ℝ) * C2 * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) :=
            le_mul_of_one_le_right (by positivity) hLq1
          calc KA * (Submission.Aseq M0 : ℝ)
                + (Submission.Aseq M0 : ℝ) * C2 * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ)
              ≤ KA * (Submission.Aseq M0 : ℝ) * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ)
                + (Submission.Aseq M0 : ℝ) * C2 * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) := by
                linarith
            _ = (KA * (Submission.Aseq M0 : ℝ) + (Submission.Aseq M0 : ℝ) * C2)
                * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) := by ring
        rw [hKsmdef]
        calc Submission.ASP.RemainderSum (rtildeFull FIr FIg FIgtil FIa) (Submission.Rcut x) m
            ≤ _ + Acount (atil FIa) (m:ℝ)
                * (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
                    ((d.divisors.card : ℝ)) ^ (5:ℕ) * FIgtil d) := hdecomp
          _ ≤ KA * (Submission.Aseq M0 : ℝ)
                + (Submission.Aseq M0 : ℝ) * (C2 * (Real.log (x:ℝ))^K2) :=
                add_le_add hAsmall h4
          _ ≤ KA * (Submission.Aseq M0 : ℝ)
                + (Submission.Aseq M0 : ℝ) * C2 * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) :=
                add_le_add le_rfl h5
          _ ≤ (KA * (Submission.Aseq M0 : ℝ) + (Submission.Aseq M0 : ℝ) * C2)
                * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) := h7
      refine le_trans htot ?_
      have hXt2x : Xt2 ≤ (x : ℝ) :=
        le_trans (Nat.le_ceil Xt2) (by exact_mod_cast hxt2)
      have hthr : (Ksm / c') * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ + 3) ≤ (x:ℝ) ^ ((15:ℝ)/64) :=
        ht2 (x:ℝ) hXt2x
      have hkey := logpow_le_of_threshold hlogx1 hc'0 hthr
      have hpow : (x:ℝ) ^ ((15:ℝ)/64) ≤ (x:ℝ) ^ ((3:ℝ)/4) :=
        Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
      have hmul : c' * (x:ℝ) ^ ((15:ℝ)/64) ≤ Acount (atil FIa) (x:ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left hpow (le_of_lt hc'0)) hcx
      calc Ksm * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ)
          ≤ c' * (x:ℝ) ^ ((15:ℝ)/64) * (Real.log (x:ℝ)) ^ (-(3:ℝ)) := hkey
        _ ≤ Acount (atil FIa) (x:ℝ) * (Real.log (x:ℝ)) ^ (-(3:ℝ)) :=
            mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg hlogxnn _)
    · -- the large scales: (2.1) at scale `m`
      push_neg at hsmall
      have hm2 : 2 ≤ m := le_trans (le_trans (by norm_num : 2 ≤ 3) hM0_3) hsmall
      have hm3 : 3 ≤ m := le_trans hM0_3 hsmall
      have hmX1 : X1 ≤ (m:ℝ) := le_trans hX1le (by exact_mod_cast hsmall)
      have hm_le_x : (m:ℝ) ≤ (x:ℝ) := by
        have h1 : ((m:ℝ)) < ((Submission.Rcut x : ℕ) : ℝ) := by exact_mod_cast hDm
        have h2 : ((Submission.Rcut x : ℕ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast hDle
        linarith
      have hAseqm : (Submission.Aseq m : ℝ) ≤ CF * (x:ℝ) ^ ((33:ℝ)/64) := by
        have h1 := hCFb m (by omega : 1 ≤ m)
        have h2 := rpow_three_quarters_le hDm
        calc (Submission.Aseq m : ℝ) ≤ CF * (m:ℝ)^((3:ℝ)/4) := h1
          _ ≤ CF * (x:ℝ)^((33:ℝ)/64) := mul_le_mul_of_nonneg_left h2 (le_of_lt hCF)
      have hAseqm0 : (0:ℝ) ≤ (Submission.Aseq m : ℝ) := by positivity
      have hTermA := termA_le_large h21raw hmX1 hm2 (le_of_lt hDm)
      have hlogm : Real.log (m:ℝ) ^ B1 ≤ Ctc * (Real.log (x:ℝ)) ^ N1 := by
        rw [hCtcdef, hN1def]
        exact logpow_le_const_mul (by exact_mod_cast hm3) hm_le_x
      have hTermB := termB_le h22raw (le_of_lt hC2) hK2 hD1 hDle hD2
      have hlogm1 : 1 ≤ Real.log (m:ℝ) :=
        le_trans one_le_log_three (Real.log_le_log (by norm_num) (by exact_mod_cast hm3))
      have hLm0 : (0:ℝ) ≤ Real.log (m:ℝ) ^ B1 :=
        Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hlogm1)) _
      have hXp0 : (0:ℝ) ≤ (x:ℝ)^((33:ℝ)/64) := by positivity
      have hLp0 : (0:ℝ) ≤ (Real.log (x:ℝ))^N1 := by positivity
      have hLp1 : (1:ℝ) ≤ (Real.log (x:ℝ))^N1 := by
        rw [← Real.rpow_natCast]
        exact Real.one_le_rpow hlogx1 (Nat.cast_nonneg _)
      have hLq1 : (1:ℝ) ≤ (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) := one_le_pow₀ hlogx1
      have hLq0 : (0:ℝ) ≤ (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) := by positivity
      have hK2le : (Real.log (x:ℝ)) ^ K2 ≤ (Real.log (x:ℝ)) ^ ((⌈K2⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogx1 (Nat.le_ceil K2)
      rw [Real.rpow_natCast] at hK2le
      -- the two summands, each absorbed into the corresponding piece of `Kc`
      have hTA : C1 * (Submission.Aseq m : ℝ) * Real.log (m:ℝ) ^ B1
          ≤ C1 * CF * Ctc * (x:ℝ)^((33:ℝ)/64) * (Real.log (x:ℝ)) ^ (N1 + ⌈K2⌉₊ : ℕ) := by
        have h1 : C1 * (Submission.Aseq m : ℝ) ≤ C1 * CF * (x:ℝ)^((33:ℝ)/64) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hAseqm (le_of_lt hC1)
        have h2 : C1 * (Submission.Aseq m : ℝ) * Real.log (m:ℝ) ^ B1
            ≤ (C1 * CF * (x:ℝ)^((33:ℝ)/64)) * (Ctc * (Real.log (x:ℝ))^N1) :=
          mul_le_mul h1 hlogm hLm0 (by positivity)
        have h4 : (0:ℝ) ≤ C1 * CF * (x:ℝ)^((33:ℝ)/64) := by positivity
        have h5 : Ctc * (Real.log (x:ℝ))^N1
            ≤ Ctc * (Real.log (x:ℝ)) ^ (N1 + ⌈K2⌉₊ : ℕ) := by
          have h5a : Ctc * (Real.log (x:ℝ))^N1
              ≤ Ctc * (Real.log (x:ℝ))^N1 * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ) :=
            le_mul_of_one_le_right (by positivity) hLq1
          refine le_trans h5a (le_of_eq ?_)
          rw [mul_assoc, ← pow_add]
        have h6 := mul_le_mul_of_nonneg_left h5 h4
        refine le_trans (le_trans h2 h6) (le_of_eq ?_)
        ring
      have hTB : (Submission.Aseq m : ℝ) * (C2 * (Real.log (x:ℝ)) ^ K2)
          ≤ CF * C2 * (x:ℝ)^((33:ℝ)/64) * (Real.log (x:ℝ)) ^ (N1 + ⌈K2⌉₊ : ℕ) := by
        have h1 : (Submission.Aseq m : ℝ) * (C2 * (Real.log (x:ℝ)) ^ K2)
            ≤ (CF * (x:ℝ)^((33:ℝ)/64)) * (C2 * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ)) :=
          mul_le_mul hAseqm (mul_le_mul_of_nonneg_left hK2le (le_of_lt hC2))
            (by positivity) (by positivity)
        have h5 : (C2 * (Real.log (x:ℝ)) ^ (⌈K2⌉₊ : ℕ))
            ≤ C2 * (Real.log (x:ℝ)) ^ (N1 + ⌈K2⌉₊ : ℕ) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hlogx1 (Nat.le_add_left ⌈K2⌉₊ N1)) (le_of_lt hC2)
        have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ CF * (x:ℝ)^((33:ℝ)/64))
        refine le_trans (le_trans h1 h6) (le_of_eq ?_)
        ring
      have htot : Submission.ASP.RemainderSum (rtildeFull FIr FIg FIgtil FIa) (Submission.Rcut x) m
          ≤ Kc * (x:ℝ)^((33:ℝ)/64) * (Real.log (x:ℝ)) ^ (N1 + ⌈K2⌉₊ : ℕ) := by
        have h4 : Acount (atil FIa) (m:ℝ)
              * (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
                  ((d.divisors.card : ℝ)) ^ (5:ℕ) * FIgtil d)
            ≤ (Submission.Aseq m : ℝ) * (C2 * (Real.log (x:ℝ))^K2) :=
          mul_le_mul (Acount_atil_le_Aseq m) hTermB hSB0 hAseqm0
        have h8 : (C1 * CF * Ctc * (x:ℝ)^((33:ℝ)/64) * (Real.log (x:ℝ)) ^ (N1 + ⌈K2⌉₊ : ℕ))
              + (CF * C2 * (x:ℝ)^((33:ℝ)/64) * (Real.log (x:ℝ)) ^ (N1 + ⌈K2⌉₊ : ℕ))
            = Kc * (x:ℝ)^((33:ℝ)/64) * (Real.log (x:ℝ)) ^ (N1 + ⌈K2⌉₊ : ℕ) := by
          rw [hKcdef]; ring
        exact le_trans hdecomp (le_trans (add_le_add hTermA h4)
          (le_trans (add_le_add hTA hTB) (le_of_eq h8)))
      refine le_trans htot ?_
      have hXt1x : Xt1 ≤ (x : ℝ) :=
        le_trans (Nat.le_ceil Xt1) (by exact_mod_cast hxt1)
      have hthr : (Kc / c') * (Real.log (x:ℝ)) ^ (N1 + ⌈K2⌉₊ + 3) ≤ (x:ℝ) ^ ((15:ℝ)/64) :=
        ht1 (x:ℝ) hXt1x
      have hkey := logpow_le_of_threshold (N := N1 + ⌈K2⌉₊) hlogx1 hc'0 hthr
      have hpow : (x:ℝ) ^ ((15:ℝ)/64) ≤ (x:ℝ) ^ ((3:ℝ)/4) :=
        Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
      have hxpow : (x:ℝ)^((15:ℝ)/64) * (x:ℝ)^((33:ℝ)/64) = (x:ℝ)^((3:ℝ)/4) := by
        rw [← Real.rpow_add (by positivity)]
        norm_num
      calc Kc * (x:ℝ)^((33:ℝ)/64) * (Real.log (x:ℝ)) ^ (N1 + ⌈K2⌉₊ : ℕ)
          = (Kc * (Real.log (x:ℝ)) ^ (N1 + ⌈K2⌉₊ : ℕ)) * (x:ℝ)^((33:ℝ)/64) := by ring
        _ ≤ (c' * (x:ℝ) ^ ((15:ℝ)/64) * (Real.log (x:ℝ)) ^ (-(3:ℝ)))
              * (x:ℝ)^((33:ℝ)/64) :=
            mul_le_mul_of_nonneg_right hkey (by positivity)
        _ = c' * (x:ℝ) ^ ((3:ℝ)/4) * (Real.log (x:ℝ)) ^ (-(3:ℝ)) := by
            rw [show c' * (x:ℝ)^((15:ℝ)/64) * (Real.log (x:ℝ))^(-(3:ℝ)) * (x:ℝ)^((33:ℝ)/64)
                = c' * ((x:ℝ)^((15:ℝ)/64) * (x:ℝ)^((33:ℝ)/64))
                  * (Real.log (x:ℝ))^(-(3:ℝ)) by ring,
              hxpow]
        _ ≤ Acount (atil FIa) (x:ℝ) * (Real.log (x:ℝ)) ^ (-(3:ℝ)) :=
            mul_le_mul_of_nonneg_right hcx (Real.rpow_nonneg hlogxnn _)

end

end Work.FIChain
