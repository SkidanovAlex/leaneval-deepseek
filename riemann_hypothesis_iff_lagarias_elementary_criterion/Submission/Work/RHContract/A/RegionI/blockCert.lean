import Mathlib
import Submission.Work.RHContract.A.RegionI.Defs
import Submission.Work.RHContract.A.RegionI.altLog_bounds
import Submission.Work.RHContract.A.RegionI.cF_basic
import Submission.Work.RHContract.A.RegionI.caExp_ge_of_le_x
import Submission.Work.RHContract.A.RegionI.caExp_le_of_gt_y
import Submission.Work.RHContract.A.RegionI.caExp_le_K
import Submission.Work.RHContract.A.RegionI.gamma_gt_57721

/-!
# Region I: Robin's inequality at `N_ε` from certified level data

This file proves `robinBound_of_levels`.  The vocabulary is that of
`Submission.Work.RHContract.A.RegionI.Defs` (`Flo`, `Fhi`, `logLowQ`, `logUpQ`,
`caS`, `cF`, `s2small`, `bsmall`), and the level-function facts of
`Submission.Work.RHContract.A.RegionI.cF_basic`.

The self-contained certified rational `log`-bounds (`logLowQ_le`, `le_logUpQ`) and the two
bridges `Flo_le_cF`, `cF_le_Fhi` are reproved here so that this module does not depend on
`Submission.Work.RHContract.A.RegionI.Core`.
-/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

noncomputable section

/-! ## Certified rational bounds for `log` -/

private lemma altLog_castQ (t : ℚ) (N : ℕ) :
    ((Work.RHContract.RegionI.altLog t N : ℚ) : ℝ)
      = ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * (t : ℝ) ^ (i + 1) / ((i + 1 : ℕ) : ℝ) := by
  unfold Work.RHContract.RegionI.altLog
  push_cast
  rfl

private lemma log2LoQ_le' : ((Work.RHContract.RegionI.log2LoQ : ℚ) : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  have h2 : ((Work.RHContract.RegionI.log2LoQ : ℚ) : ℝ) ≤ (6931471803 : ℝ) / 10 ^ 10 := by
    rw [Work.RHContract.RegionI.log2LoQ]; norm_num
  linarith

private lemma log2UpQ_ge' : Real.log 2 ≤ ((Work.RHContract.RegionI.log2UpQ : ℚ) : ℝ) := by
  have h := Real.log_two_lt_d9
  have h2 : (6931471809 : ℝ) / 10 ^ 10 ≤ ((Work.RHContract.RegionI.log2UpQ : ℚ) : ℝ) := by
    rw [Work.RHContract.RegionI.log2UpQ]; norm_num
  linarith

private lemma log1pLo_le' {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (Work.RHContract.RegionI.log1pLo t : ℝ) ≤ Real.log (1 + (t : ℝ)) := by
  unfold Work.RHContract.RegionI.log1pLo
  have ht : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h0
  by_cases hA : t ≤ 1 / 1024
  · rw [if_pos hA]
    have h2 : (t : ℝ) ≤ 1 / 2 := by
      have hq : t ≤ (1 : ℚ) / 2 := le_trans hA (by norm_num)
      have hc : ((t : ℚ) : ℝ) ≤ (((1 : ℚ) / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
      norm_num at hc
      exact hc
    have h := (altLog_bounds (t := (t : ℝ)) ht h2 4).1 (by norm_num)
    rw [altLog_castQ]; exact h
  · rw [if_neg hA]
    by_cases hB : t ≤ 1 / 32
    · rw [if_pos hB]
      have h2 : (t : ℝ) ≤ 1 / 2 := by
        have hq : t ≤ (1 : ℚ) / 2 := le_trans hB (by norm_num)
        have hc : ((t : ℚ) : ℝ) ≤ (((1 : ℚ) / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
        norm_num at hc
        exact hc
      have h := (altLog_bounds (t := (t : ℝ)) ht h2 10).1 (by norm_num)
      rw [altLog_castQ]; exact h
    · rw [if_neg hB]
      by_cases hC : t ≤ 1 / 2
      · rw [if_pos hC]
        have h2 : (t : ℝ) ≤ 1 / 2 := by
          have hc : ((t : ℚ) : ℝ) ≤ (((1 : ℚ) / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hC
          norm_num at hc
          exact hc
        have h := (altLog_bounds (t := (t : ℝ)) ht h2 46).1 (by norm_num)
        rw [altLog_castQ]; exact h
      · rw [if_neg hC]
        exact Commons.NumberTheory.Robin.RobinCaFval.logOneAddLower_le_log_one_add t h0

private lemma le_log1pUp' {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.log (1 + (t : ℝ)) ≤ (Work.RHContract.RegionI.log1pUp t : ℝ) := by
  unfold Work.RHContract.RegionI.log1pUp
  have ht : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h0
  by_cases hA : t ≤ 1 / 1024
  · rw [if_pos hA]
    have h2 : (t : ℝ) ≤ 1 / 2 := by
      have hq : t ≤ (1 : ℚ) / 2 := le_trans hA (by norm_num)
      have hc : ((t : ℚ) : ℝ) ≤ (((1 : ℚ) / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
      norm_num at hc
      exact hc
    have h := (altLog_bounds (t := (t : ℝ)) ht h2 5).2 (by norm_num)
    rw [altLog_castQ]; exact h
  · rw [if_neg hA]
    by_cases hB : t ≤ 1 / 32
    · rw [if_pos hB]
      have h2 : (t : ℝ) ≤ 1 / 2 := by
        have hq : t ≤ (1 : ℚ) / 2 := le_trans hB (by norm_num)
        have hc : ((t : ℚ) : ℝ) ≤ (((1 : ℚ) / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
        norm_num at hc
        exact hc
      have h := (altLog_bounds (t := (t : ℝ)) ht h2 11).2 (by norm_num)
      rw [altLog_castQ]; exact h
    · rw [if_neg hB]
      by_cases hC : t ≤ 1 / 2
      · rw [if_pos hC]
        have h2 : (t : ℝ) ≤ 1 / 2 := by
          have hc : ((t : ℚ) : ℝ) ≤ (((1 : ℚ) / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hC
          norm_num at hc
          exact hc
        have h := (altLog_bounds (t := (t : ℝ)) ht h2 47).2 (by norm_num)
        rw [altLog_castQ]; exact h
      · rw [if_neg hC]
        exact Commons.NumberTheory.Robin.RobinCaFval.logOneAddUpper_ge_log_one_add t h0

private lemma logLowAuxQ_le' (k : ℕ) (x : ℚ) (h1 : 1 ≤ x) (h2 : x < 2 ^ k) :
    (Work.RHContract.RegionI.logLowAuxQ x k : ℝ) ≤ Real.log (x : ℝ) := by
  induction k generalizing x with
  | zero =>
      have : (x : ℚ) < 1 := by simpa using h2
      linarith
  | succ k ih =>
      by_cases hx : x < 2
      · rw [Work.RHContract.RegionI.logLowAuxQ, if_pos hx]
        have h0 : (0 : ℚ) ≤ x - 1 := by linarith
        have hlt : x - 1 ≤ 1 := by linarith
        have h := log1pLo_le' h0 hlt
        have hxr : (1 : ℝ) + ((x - 1 : ℚ) : ℝ) = (x : ℝ) := by push_cast; ring
        rwa [hxr] at h
      · rw [Work.RHContract.RegionI.logLowAuxQ, if_neg hx]
        push_cast
        have hx2 : 2 ≤ x := le_of_not_gt hx
        have hxpos : (0 : ℚ) < x := lt_of_lt_of_le one_pos h1
        have hhalf1 : 1 ≤ x / 2 := by
          rw [le_div_iff₀ (by norm_num : (0:ℚ) < 2)]; linarith
        have hhalf2 : x / 2 < 2 ^ k := by
          rw [div_lt_iff₀ (by norm_num : (0:ℚ) < 2)]
          simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h2
        have hih := ih (x / 2) hhalf1 hhalf2
        have hlogeq : Real.log (x : ℝ) = Real.log 2 + Real.log ((x / 2 : ℚ) : ℝ) := by
          have hx2' : (x : ℝ) = 2 * ((x / 2 : ℚ) : ℝ) := by push_cast; ring
          rw [hx2', Real.log_mul (by norm_num) (by positivity)]
        rw [hlogeq]
        linarith [log2LoQ_le', hih]

private lemma logUpAuxQ_ge' (k : ℕ) (x : ℚ) (h1 : 1 ≤ x) (h2 : x < 2 ^ k) :
    Real.log (x : ℝ) ≤ (Work.RHContract.RegionI.logUpAuxQ x k : ℝ) := by
  induction k generalizing x with
  | zero =>
      have : (x : ℚ) < 1 := by simpa using h2
      linarith
  | succ k ih =>
      by_cases hx : x < 2
      · rw [Work.RHContract.RegionI.logUpAuxQ, if_pos hx]
        have h0 : (0 : ℚ) ≤ x - 1 := by linarith
        have hlt : x - 1 ≤ 1 := by linarith
        have h := le_log1pUp' h0 hlt
        have hxr : (1 : ℝ) + ((x - 1 : ℚ) : ℝ) = (x : ℝ) := by push_cast; ring
        rwa [hxr] at h
      · rw [Work.RHContract.RegionI.logUpAuxQ, if_neg hx]
        push_cast
        have hx2 : 2 ≤ x := le_of_not_gt hx
        have hxpos : (0 : ℚ) < x := lt_of_lt_of_le one_pos h1
        have hhalf1 : 1 ≤ x / 2 := by
          rw [le_div_iff₀ (by norm_num : (0:ℚ) < 2)]; linarith
        have hhalf2 : x / 2 < 2 ^ k := by
          rw [div_lt_iff₀ (by norm_num : (0:ℚ) < 2)]
          simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h2
        have hih := ih (x / 2) hhalf1 hhalf2
        have hlogeq : Real.log (x : ℝ) = Real.log 2 + Real.log ((x / 2 : ℚ) : ℝ) := by
          have hx2' : (x : ℝ) = 2 * ((x / 2 : ℚ) : ℝ) := by push_cast; ring
          rw [hx2', Real.log_mul (by norm_num) (by positivity)]
        rw [hlogeq]
        linarith [log2UpQ_ge', hih]

private lemma logLowQ_le' {x : ℚ} (h1 : 1 ≤ x) (h2 : x < 2 ^ 20) :
    (Work.RHContract.RegionI.logLowQ x : ℝ) ≤ Real.log (x : ℝ) :=
  logLowAuxQ_le' 26 x h1 (by norm_num at h2 ⊢; linarith)

private lemma le_logUpQ' {x : ℚ} (h1 : 1 ≤ x) (h2 : x < 2 ^ 20) :
    Real.log (x : ℝ) ≤ (Work.RHContract.RegionI.logUpQ x : ℝ) :=
  logUpAuxQ_ge' 26 x h1 (by norm_num at h2 ⊢; linarith)

private lemma cFr_castQ (p k : ℕ) :
    ((Work.RHContract.RegionI.cFr p k : ℚ) : ℝ)
      = ((p : ℝ) ^ (k + 1) - 1) / ((p : ℝ) ^ (k + 1) - (p : ℝ)) := by
  unfold Work.RHContract.RegionI.cFr
  push_cast
  rfl

private lemma cFr_eq' {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    Work.RHContract.RegionI.cFr p k = 1 + 1 / (Work.RHContract.RegionI.caS p k : ℚ) := by
  apply Rat.cast_injective (α := ℝ)
  rw [cFr_castQ]
  push_cast
  rw [cFBasic.ratio_eq_one_add_inv_caS hp hk]

private lemma one_le_cFr' {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (1 : ℚ) ≤ Work.RHContract.RegionI.cFr p k := by
  rw [cFr_eq' hp hk]
  have h : (1 : ℚ) ≤ (Work.RHContract.RegionI.caS p k : ℚ) := by
    exact_mod_cast cFBasic.caS_pos (by omega) hk
  have h2 : (0 : ℚ) ≤ 1 / (Work.RHContract.RegionI.caS p k : ℚ) := by positivity
  linarith

private lemma cFr_le_two' {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    Work.RHContract.RegionI.cFr p k ≤ 2 := by
  rw [cFr_eq' hp hk]
  have h : (1 : ℚ) ≤ (Work.RHContract.RegionI.caS p k : ℚ) := by
    exact_mod_cast cFBasic.caS_pos (by omega) hk
  have hpos : (0 : ℚ) < (Work.RHContract.RegionI.caS p k : ℚ) := lt_of_lt_of_le one_pos h
  have : 1 / (Work.RHContract.RegionI.caS p k : ℚ) ≤ 1 := by
    rw [div_le_one hpos]; exact h
  linarith

private theorem Flo_le_cF' {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) (hpb : p < 2 ^ 20) :
    (Work.RHContract.RegionI.Flo p k : ℝ) ≤ Work.RHContract.RegionI.cF p k := by
  have h1 : (1 : ℚ) ≤ Work.RHContract.RegionI.cFr p k := one_le_cFr' hp hk
  have h2 : Work.RHContract.RegionI.cFr p k < 2 ^ 20 :=
    lt_of_le_of_lt (cFr_le_two' hp hk) (by norm_num)
  have h3 : (Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.cFr p k) : ℝ)
      ≤ Real.log (((Work.RHContract.RegionI.cFr p k : ℚ) : ℝ)) := logLowQ_le' h1 h2
  have h4 : Real.log ((p : ℚ) : ℝ) ≤ (Work.RHContract.RegionI.logUpQ (p : ℚ) : ℝ) :=
    le_logUpQ' (by exact_mod_cast (by omega : 1 ≤ p)) (by exact_mod_cast hpb)
  have hLp : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hUp : (0 : ℝ) < (Work.RHContract.RegionI.logUpQ (p : ℚ) : ℝ) := lt_of_lt_of_le hLp h4
  have hA : (0 : ℝ) ≤ Real.log (((Work.RHContract.RegionI.cFr p k : ℚ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast h1)
  calc (Work.RHContract.RegionI.Flo p k : ℝ)
        = (Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.cFr p k) : ℝ)
            / (Work.RHContract.RegionI.logUpQ (p : ℚ) : ℝ) := by
          simp only [Work.RHContract.RegionI.Flo, Rat.cast_div]
    _ ≤ Real.log (((Work.RHContract.RegionI.cFr p k : ℚ) : ℝ))
            / (Work.RHContract.RegionI.logUpQ (p : ℚ) : ℝ) :=
        div_le_div_of_nonneg_right h3 (le_of_lt hUp)
    _ ≤ Real.log (((Work.RHContract.RegionI.cFr p k : ℚ) : ℝ)) / Real.log (p : ℝ) :=
        div_le_div_of_nonneg_left hA hLp h4
    _ = Work.RHContract.RegionI.cF p k := by rw [Work.RHContract.RegionI.cF, cFr_castQ]

private theorem cF_le_Fhi' {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) (hpb : p < 2 ^ 20)
    (hpos : (0 : ℚ) < Work.RHContract.RegionI.logLowQ (p : ℚ)) :
    Work.RHContract.RegionI.cF p k ≤ (Work.RHContract.RegionI.Fhi p k : ℝ) := by
  have h1 : (1 : ℚ) ≤ Work.RHContract.RegionI.cFr p k := one_le_cFr' hp hk
  have h2 : Work.RHContract.RegionI.cFr p k < 2 ^ 20 :=
    lt_of_le_of_lt (cFr_le_two' hp hk) (by norm_num)
  have h3 : Real.log (((Work.RHContract.RegionI.cFr p k : ℚ) : ℝ))
      ≤ (Work.RHContract.RegionI.logUpQ (Work.RHContract.RegionI.cFr p k) : ℝ) := le_logUpQ' h1 h2
  have h4 : (Work.RHContract.RegionI.logLowQ (p : ℚ) : ℝ) ≤ Real.log (p : ℝ) :=
    logLowQ_le' (by exact_mod_cast (by omega : 1 ≤ p)) (by exact_mod_cast hpb)
  have h5 : (0 : ℝ) < (Work.RHContract.RegionI.logLowQ (p : ℚ) : ℝ) := by exact_mod_cast hpos
  have hLp : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hA : (0 : ℝ) ≤ Real.log (((Work.RHContract.RegionI.cFr p k : ℚ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast h1)
  calc Work.RHContract.RegionI.cF p k
        = Real.log (((Work.RHContract.RegionI.cFr p k : ℚ) : ℝ)) / Real.log (p : ℝ) := by
          rw [Work.RHContract.RegionI.cF, cFr_castQ]
    _ ≤ Real.log (((Work.RHContract.RegionI.cFr p k : ℚ) : ℝ))
            / (Work.RHContract.RegionI.logLowQ (p : ℚ) : ℝ) :=
        div_le_div_of_nonneg_left hA h5 h4
    _ ≤ (Work.RHContract.RegionI.logUpQ (Work.RHContract.RegionI.cFr p k) : ℝ)
            / (Work.RHContract.RegionI.logLowQ (p : ℚ) : ℝ) :=
        div_le_div_of_nonneg_right h3 (le_of_lt h5)
    _ = (Work.RHContract.RegionI.Fhi p k : ℝ) := by
          simp only [Work.RHContract.RegionI.Fhi, Rat.cast_div]

/-! ## `s2small` -/

private lemma smallP_toFinset' (N : ℕ) : (Work.RHContract.RegionI.smallP N).toFinset
    = Nat.primesLE N := by
  ext p
  simp only [List.mem_toFinset, Work.RHContract.RegionI.smallP, List.mem_filter, List.mem_range,
    Nat.mem_primesLE, Work.RHContract.RegionI.isP_iff, Nat.lt_succ_iff]

private lemma s2small_spec' (N : ℕ) :
    (Work.RHContract.RegionI.s2small N : ℝ)
      = ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-2 : ℤ) := by
  unfold Work.RHContract.RegionI.s2small
  rw [smallP_toFinset']
  push_cast
  ring

/-! ## The support of `N_ε` -/

open Work.RHContract.RegionI (yA)

private lemma ratCast_le_real {a b : ℚ} (h : a ≤ b) : ((a : ℚ) : ℝ) ≤ ((b : ℚ) : ℝ) :=
  Rat.cast_le.mpr h


/-- The exponent `⌊caMu p ε⌋₊` of the prime `p` in `N_ε`. -/
def lev (ε : ℝ) (p : ℕ) : ℕ := ⌊Work.RHPlan.caMu p ε⌋₊

/-- `⌈e^{2/ε}⌉+2`, the prime bound in the definition of `N_ε`. -/
def caB (ε : ℝ) : ℕ := Nat.ceil (Real.exp (2 / ε)) + 2

/-- The support of `N_ε`: the primes dividing `N_ε`. -/
def caSupp (ε : ℝ) : Finset ℕ :=
  ((Finset.range (caB ε)).filter Nat.Prime).filter (fun p => 1 ≤ lev ε p)

lemma mem_caSupp {ε : ℝ} {p : ℕ} :
    p ∈ caSupp ε ↔ Nat.Prime p ∧ p < caB ε ∧ 1 ≤ lev ε p := by
  simp only [caSupp, Finset.mem_filter, Finset.mem_range]
  tauto

lemma caNumber_eq_prod (ε : ℝ) :
    Work.RHPlan.caNumber ε
      = ∏ p ∈ (Finset.range (caB ε)).filter Nat.Prime, p ^ lev ε p := rfl

lemma caNumber_pos (ε : ℝ) : 0 < Work.RHPlan.caNumber ε := by
  rw [caNumber_eq_prod]
  exact Finset.prod_pos (fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _)

lemma caNumber_ne_zero (ε : ℝ) : Work.RHPlan.caNumber ε ≠ 0 := ne_of_gt (caNumber_pos ε)

lemma log_caNumber_eq_prod (ε : ℝ) :
    Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)
      = ∑ p ∈ (Finset.range (caB ε)).filter Nat.Prime, (lev ε p : ℝ) * Real.log (p : ℝ) := by
  rw [caNumber_eq_prod]
  push_cast
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Real.log_pow]
  · intro p hp
    exact_mod_cast (ne_of_gt (pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) (lev ε p)))

lemma lev_eq_zero_of_caB_le {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : 2 ≤ p) (h : caB ε ≤ p) :
    lev ε p = 0 := by
  have := Commons.NumberTheory.Robin.caExp_eq_zero_of_ge_bound p ε hp hε h
  simpa only [lev, caB, Work.RHPlan.caMu] using this

/-! ## The log-decomposition of `N_ε` -/

private lemma sigma_prod_prime_pows {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    (a : ℕ → ℕ) :
    ArithmeticFunction.sigma 1 (∏ p ∈ s, p ^ a p)
      = ∏ p ∈ s, ArithmeticFunction.sigma 1 (p ^ a p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hpnot ih =>
      have hp' : Nat.Prime p := hprime p (by simp)
      have hcop : (p ^ a p).Coprime (∏ q ∈ s, q ^ a q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        have hq' : Nat.Prime q := hprime q (Finset.mem_insert_of_mem hq)
        have hpq_ne : q ≠ p := fun hpq => hpnot (by simpa [hpq] using hq)
        have hpq : p.Coprime q := (Nat.coprime_primes hp' hq').mpr (Ne.symm hpq_ne)
        have h1 : p.Coprime (q ^ a q) := Nat.Coprime.pow_right (a q) hpq
        exact Nat.Coprime.pow_left (a p) h1
      have hσ := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
      have ih' := ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
      rw [Finset.prod_insert hpnot, hσ, ih', Finset.prod_insert hpnot]

private lemma log_sigma_pow_sub {p a : ℕ} (hp : Nat.Prime p) :
    Real.log (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ)) - (a : ℝ) * Real.log (p : ℝ)
      = Real.log ((p : ℝ) / ((p : ℝ) - 1))
        + Real.log ((((p : ℝ) ^ (a + 1)) - 1) / ((p : ℝ) ^ (a + 1))) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpa : (0 : ℝ) < (p : ℝ) ^ a := by positivity
  have hpa1 : (0 : ℝ) < (p : ℝ) ^ (a + 1) := by positivity
  have hnum : (0 : ℝ) < (p : ℝ) ^ (a + 1) - 1 := by
    have : (1 : ℝ) < (p : ℝ) ^ (a + 1) := one_lt_pow₀ hp1 (by omega)
    linarith
  have hσpos : (0 : ℝ) < ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 (p ^ a) (ne_of_gt (pow_pos hp.pos a))
  have hlogpa : Real.log ((p : ℝ) ^ a) = (a : ℝ) * Real.log (p : ℝ) := Real.log_pow p a
  have hratio := Commons.NumberTheory.Robin.sigma_one_ratio_prime_pow (p := p) (k := a) hp
  have hkey : Real.log (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ))
      = Real.log ((((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) / (p : ℝ) ^ a)
          * (p : ℝ) ^ a) := by
    rw [div_mul_cancel₀ _ hpa.ne']
  rw [hkey, Real.log_mul (div_ne_zero hσpos.ne' hpa.ne') hpa.ne', hratio]
  have hdecomp : ((p : ℝ) ^ (a + 1) - 1) / ((p : ℝ) ^ a * ((p : ℝ) - 1))
      = (((p : ℝ) ^ (a + 1) - 1) / ((p : ℝ) ^ (a + 1))) * ((p : ℝ) / ((p : ℝ) - 1)) := by
    field_simp
    ring
  rw [hdecomp, Real.log_mul (by positivity) (by positivity), hlogpa]
  ring

/-- **The log-decomposition of `N_ε`.**  `log(σ(N_ε)/N_ε)` is the sum of the Mertens part
`Σ_{p ∈ supp} log(p/(p-1))` and the correction part `Σ_{p ∈ supp} log(1 - p^{-(a_p+1)})`. -/
theorem log_sigma_div_eq (ε : ℝ) (hε : 0 < ε) :
    Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)
        / ((Work.RHPlan.caNumber ε : ℕ) : ℝ))
      = (∑ p ∈ caSupp ε, Real.log ((p : ℝ) / ((p : ℝ) - 1)))
        + ∑ p ∈ caSupp ε,
            Real.log ((((p : ℝ) ^ (lev ε p + 1)) - 1) / ((p : ℝ) ^ (lev ε p + 1))) := by
  have hN : ((Work.RHPlan.caNumber ε : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (caNumber_pos ε))
  have hσ : (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ)) : ℝ) ≠ 0 := by
    have := ArithmeticFunction.sigma_pos 1 (Work.RHPlan.caNumber ε) (ne_of_gt (caNumber_pos ε))
    exact_mod_cast (ne_of_gt this)
  have hlogσ : Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ))
      = ∑ p ∈ (Finset.range (caB ε)).filter Nat.Prime,
          Real.log (((ArithmeticFunction.sigma 1 (p ^ lev ε p) : ℕ) : ℝ)) := by
    have hfac := sigma_prod_prime_pows (s := (Finset.range (caB ε)).filter Nat.Prime)
      (fun p hp => (Finset.mem_filter.mp hp).2) (fun p => lev ε p)
    have hcast : ((∏ p ∈ (Finset.range (caB ε)).filter Nat.Prime,
        ArithmeticFunction.sigma 1 (p ^ lev ε p) : ℕ) : ℝ)
        = ∏ p ∈ (Finset.range (caB ε)).filter Nat.Prime,
            ((ArithmeticFunction.sigma 1 (p ^ lev ε p) : ℕ) : ℝ) := by
      push_cast
      ring
    rw [caNumber_eq_prod, hfac, hcast, Real.log_prod]
    intro p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hpos : 0 < ArithmeticFunction.sigma 1 (p ^ lev ε p) :=
      ArithmeticFunction.sigma_pos 1 (p ^ lev ε p) (ne_of_gt (pow_pos hpp.pos _))
    exact_mod_cast (ne_of_gt hpos)
  have hlogN := log_caNumber_eq_prod ε
  rw [Real.log_div hσ hN, hlogσ, hlogN, ← Finset.sum_sub_distrib]
  have hpt : ∀ p ∈ (Finset.range (caB ε)).filter Nat.Prime,
      Real.log (((ArithmeticFunction.sigma 1 (p ^ lev ε p) : ℕ) : ℝ))
          - (lev ε p : ℝ) * Real.log (p : ℝ)
        = Real.log ((p : ℝ) / ((p : ℝ) - 1))
          + Real.log ((((p : ℝ) ^ (lev ε p + 1)) - 1) / ((p : ℝ) ^ (lev ε p + 1))) :=
    fun p hp => log_sigma_pow_sub (Finset.mem_filter.mp hp).2
  rw [show (∑ p ∈ (Finset.range (caB ε)).filter Nat.Prime,
        (Real.log (((ArithmeticFunction.sigma 1 (p ^ lev ε p) : ℕ) : ℝ))
          - (lev ε p : ℝ) * Real.log (p : ℝ)))
      = ∑ p ∈ (Finset.range (caB ε)).filter Nat.Prime,
        (Real.log ((p : ℝ) / ((p : ℝ) - 1))
          + Real.log ((((p : ℝ) ^ (lev ε p + 1)) - 1) / ((p : ℝ) ^ (lev ε p + 1))))
      from Finset.sum_congr rfl hpt]
  have hv : ∀ p ∈ (Finset.range (caB ε)).filter Nat.Prime, p ∉ caSupp ε →
      Real.log ((p : ℝ) / ((p : ℝ) - 1))
        + Real.log ((((p : ℝ) ^ (lev ε p + 1)) - 1) / ((p : ℝ) ^ (lev ε p + 1))) = 0 := by
    intro p hp hnp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hlev : lev ε p = 0 := by
      by_contra hcon
      exact hnp (mem_caSupp.mpr ⟨hpp, Finset.mem_range.mp (Finset.mem_filter.mp hp).1,
        by omega⟩)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hb : (((p : ℝ) ^ (lev ε p + 1)) - 1) / ((p : ℝ) ^ (lev ε p + 1)) ≠ 0 := by
      refine div_ne_zero ?_ (by positivity)
      have hlt : (1 : ℝ) < (p : ℝ) ^ (lev ε p + 1) :=
        one_lt_pow₀ (by linarith) (by omega)
      linarith
    have h1 : (p : ℝ) / ((p : ℝ) - 1)
        * (((p : ℝ) ^ (lev ε p + 1) - 1) / (p : ℝ) ^ (lev ε p + 1)) = 1 := by
      rw [hlev, pow_one, div_mul_div_comm, mul_comm ((p : ℝ) - 1) (p : ℝ),
        div_self (by positivity)]
    rw [← Real.log_mul (by positivity) hb, h1, Real.log_one]
  have hsub : caSupp ε ⊆ (Finset.range (caB ε)).filter Nat.Prime := by
    intro p hp; exact (Finset.mem_filter.mp hp).1
  rw [← Finset.sum_subset hsub hv, Finset.sum_add_distrib]

/-! ## Level bounds -/

theorem lev_ge_of_le_x
    (ε : ℝ) (hε : 0 < ε) (εT : ℚ) (hεT : ε ≤ (εT : ℝ))
    (K : ℕ) (x : Fin K → ℕ)
    (hxle : ∀ k : Fin K, εT ≤ Work.RHContract.RegionI.Flo (x k) (k.val + 1))
    (hxlo : ∀ k : Fin K, 2 ≤ x k) (hxhi : ∀ k : Fin K, x k < 2 ^ 20)
    (k : Fin K) {p : ℕ} (hp : 2 ≤ p) (hpx : p ≤ x k) : k.val + 1 ≤ lev ε p := by
  have hxc : ∀ k : Fin K, ε ≤ Work.RHContract.RegionI.cF (x k) (k.val + 1) := by
    intro k
    have h1 : (εT : ℝ) ≤ (Work.RHContract.RegionI.Flo (x k) (k.val + 1) : ℝ) :=
      Rat.cast_le.mpr (hxle k)
    have h2 : (Work.RHContract.RegionI.Flo (x k) (k.val + 1) : ℝ)
        ≤ Work.RHContract.RegionI.cF (x k) (k.val + 1) :=
      Flo_le_cF' (hxlo k) (Nat.succ_pos k.val) (hxhi k)
    linarith
  exact caExp_ge_of_le_x ε hε K x hxc hxlo k p hp hpx

/-- If `Fhi (y k + 1) (k+1) < εB < ε` then `cF (y k + 1) (k+1) < ε` for every `k`. -/
lemma cF_lt_of_Fhi_lt
    (ε : ℝ) (εB : ℚ) (hεB : (εB : ℝ) < ε)
    (K : ℕ) (y : Fin K → ℕ)
    (hylo : ∀ k : Fin K, Work.RHContract.RegionI.Fhi (y k + 1) (k.val + 1) < εB)
    (hyhi : ∀ k : Fin K, y k + 1 < 2 ^ 20) (hy1k : ∀ k : Fin K, 1 ≤ y k)
    (hposy : ∀ k : Fin K, (0 : ℚ) < Work.RHContract.RegionI.logLowQ ((y k + 1 : ℕ) : ℚ)) :
    ∀ k : Fin K, Work.RHContract.RegionI.cF (y k + 1) (k.val + 1) < ε := by
  intro k
  have h1 : (Work.RHContract.RegionI.Fhi (y k + 1) (k.val + 1) : ℝ) < ε := by
    have h2 : ((Work.RHContract.RegionI.Fhi (y k + 1) (k.val + 1) : ℚ) : ℝ) < (εB : ℝ) :=
      Rat.cast_lt.mpr (hylo k)
    linarith
  have hy1 : 2 ≤ y k + 1 := by have := hy1k k; omega
  exact lt_of_le_of_lt (cF_le_Fhi' hy1 (Nat.succ_pos k.val) (hyhi k) (hposy k)) h1

theorem lev_le_of_gt_y
    (ε : ℝ) (hε : 0 < ε) (εB : ℚ) (hεB : (εB : ℝ) < ε)
    (K : ℕ) (y : Fin K → ℕ)
    (hylo : ∀ k : Fin K, Work.RHContract.RegionI.Fhi (y k + 1) (k.val + 1) < εB)
    (hyhi : ∀ k : Fin K, y k + 1 < 2 ^ 20) (hy1k : ∀ k : Fin K, 1 ≤ y k)
    (hposy : ∀ k : Fin K, (0 : ℚ) < Work.RHContract.RegionI.logLowQ ((y k + 1 : ℕ) : ℚ))
    (k : Fin K) {p : ℕ} (hp : 2 ≤ p) (hpy : y k < p) : lev ε p ≤ k.val :=
  caExp_le_of_gt_y ε hε K y hy1k (cF_lt_of_Fhi_lt ε εB hεB K y hylo hyhi hy1k hposy)
    k p hp hpy

lemma logLowQ_two_pos : (0 : ℚ) < Work.RHContract.RegionI.logLowQ (2 : ℚ) := by
  decide +kernel

theorem lev_le_K (ε : ℝ) (hε : 0 < ε) (εB : ℚ) (hεB : (εB : ℝ) < ε) (K : ℕ) (hK : 2 ≤ K)
    (hKtop : Work.RHContract.RegionI.Fhi 2 (K + 1) < εB) :
    ∀ {p : ℕ}, 2 ≤ p → lev ε p ≤ K := by
  have h2 : Work.RHContract.RegionI.cF 2 (K + 1) < ε := by
    have h3 : (Work.RHContract.RegionI.Fhi 2 (K + 1) : ℝ) < ε := by
      have h4 : ((Work.RHContract.RegionI.Fhi 2 (K + 1) : ℚ) : ℝ) < (εB : ℝ) :=
        Rat.cast_lt.mpr hKtop
      linarith
    exact lt_of_le_of_lt (cF_le_Fhi' (by norm_num) (by omega) (by norm_num) logLowQ_two_pos) h3
  intro p hp
  exact caExp_le_K ε hε K (by omega) h2 p hp

/-! ## The Mertens part -/

private lemma mertens_le {ε : ℝ} (hε : 0 < ε) (y0 : ℕ)
    (h : ∀ p : ℕ, Nat.Prime p → 1 ≤ lev ε p → p ≤ y0) :
    (∑ p ∈ caSupp ε, Real.log ((p : ℝ) / ((p : ℝ) - 1)))
      ≤ Commons.NumberTheory.Mertens.logRatioSum (y0 : ℝ) := by
  have hsub : caSupp ε ⊆ Nat.primesLE y0 := by
    intro p hp
    obtain ⟨hpp, _, hlev⟩ := mem_caSupp.mp hp
    exact Nat.mem_primesLE.mpr ⟨h p hpp hlev, hpp⟩
  have hnonneg : ∀ p ∈ Nat.primesLE y0, p ∉ caSupp ε →
      0 ≤ Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
    intro p hp _
    have hpp : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hge1 : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    exact Real.log_nonneg hge1
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hlr : Commons.NumberTheory.Mertens.logRatioSum (y0 : ℝ)
      = ∑ p ∈ Nat.primesLE y0, Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
    unfold Commons.NumberTheory.Mertens.logRatioSum
    rw [Nat.floor_natCast]
  rw [hlr]
  exact hle

/-! ## The correction part -/

private lemma lev_le_yA {ε : ℝ} (hε : 0 < ε) (K : ℕ) (y : Fin K → ℕ)
    (hy1k : ∀ k : Fin K, 1 ≤ y k)
    (hyc : ∀ k : Fin K, Work.RHContract.RegionI.cF (y k + 1) (k.val + 1) < ε)
    (hlevK : ∀ p : ℕ, 2 ≤ p → lev ε p ≤ K)
    {p : ℕ} (hp : 2 ≤ p) : lev ε p ≤ yA y p := by
  have hkey : ∀ k : Fin K, k.val + 1 ≤ lev ε p → p ≤ y k := by
    intro k hk
    by_contra hcon
    have hlt : y k < p := lt_of_not_ge hcon
    have h := caExp_le_of_gt_y ε hε K y hy1k hyc k p hp hlt
    have h' : lev ε p ≤ k.val := h
    omega
  have hcard : (Finset.univ.filter (fun k : Fin K => k.val + 1 ≤ lev ε p)).card ≤ yA y p := by
    rw [yA]
    refine Finset.card_le_card (fun k hk => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hkey k hk
  have hcard2 : lev ε p ≤ (Finset.univ.filter (fun k : Fin K => k.val + 1 ≤ lev ε p)).card := by
    have hleK : lev ε p ≤ K := hlevK p hp
    have hinj : Function.Injective (fun j : Fin (lev ε p) =>
        (⟨⟨j.val, lt_of_lt_of_le j.isLt hleK⟩,
          Nat.succ_le_of_lt j.isLt⟩ : {k : Fin K // k.val + 1 ≤ lev ε p})) := by
      intro a b hab
      simp only [Subtype.mk.injEq, Fin.mk.injEq] at hab
      exact Fin.ext hab
    have hcard := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin, Fintype.card_subtype] at hcard
    exact hcard
  linarith

private lemma pow_neg_eq_inv (p : ℝ) (n : ℕ) :
    p ^ (-(((n : ℕ) : ℤ) + 1)) = 1 / p ^ (n + 1) := by
  have h : ((n : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, zpow_neg, zpow_natCast, inv_eq_one_div]

private lemma corr_le {ε : ℝ} (hε : 0 < ε) (Ky : ℕ) (hKy : 2 ≤ Ky) (y : Fin Ky → ℕ)
    (x0 y1 : ℕ) (hy1def : y1 = y ⟨1, by omega⟩)
    (hy1 : y1 + 1 ≤ x0) (hy1k1 : 1 ≤ y1)
    (hge0 : ∀ p : ℕ, Nat.Prime p → p ≤ x0 → 1 ≤ lev ε p)
    (hyA : ∀ p : ℕ, 2 ≤ p → lev ε p ≤ yA y p)
    (hlev1 : ∀ p : ℕ, y1 < p → lev ε p ≤ 1)
    (Sx : ℚ) (hSx : (Sx : ℝ) ≤ ∑ p ∈ Nat.primesLE x0, (p : ℝ) ^ (-2 : ℤ)) :
    (∑ p ∈ caSupp ε,
        Real.log ((((p : ℝ) ^ (lev ε p + 1)) - 1) / ((p : ℝ) ^ (lev ε p + 1))))
      ≤ -(((Work.RHContract.RegionI.bsmall y y1 : ℚ) : ℝ)
          + ((Sx : ℝ) - (Work.RHContract.RegionI.s2small y1 : ℝ))) := by
  have hsum1 : (∑ p ∈ caSupp ε,
        Real.log ((((p : ℝ) ^ (lev ε p + 1)) - 1) / ((p : ℝ) ^ (lev ε p + 1))))
      ≤ -∑ p ∈ caSupp ε, ((p : ℝ) ^ (-(((lev ε p : ℕ) : ℤ) + 1))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hpp : Nat.Prime p := (mem_caSupp.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hpow : (0 : ℝ) < (p : ℝ) ^ (lev ε p + 1) := by positivity
    have hlt1 : (p : ℝ) ^ (-(((lev ε p : ℕ) : ℤ) + 1)) < 1 := by
      rw [pow_neg_eq_inv, div_lt_one (by positivity)]
      exact one_lt_pow₀ (by linarith) (by omega)
    have hx0pos : 0 < 1 - (p : ℝ) ^ (-(((lev ε p : ℕ) : ℤ) + 1)) := by linarith
    have hlog := Real.log_le_sub_one_of_pos hx0pos
    have heq : (((p : ℝ) ^ (lev ε p + 1)) - 1) / ((p : ℝ) ^ (lev ε p + 1))
        = 1 - (p : ℝ) ^ (-(((lev ε p : ℕ) : ℤ) + 1)) := by
      rw [pow_neg_eq_inv, sub_div, div_self hpow.ne']
    rw [heq]
    linarith
  have hbs_cast : ((Work.RHContract.RegionI.bsmall y y1 : ℚ) : ℝ)
      = ∑ p ∈ Nat.primesLE y1, (p : ℝ) ^ (-(((yA y p : ℕ) : ℤ) + 1)) := by
    unfold Work.RHContract.RegionI.bsmall
    rw [smallP_toFinset']
    push_cast
    rfl
  have hbs : ((Work.RHContract.RegionI.bsmall y y1 : ℚ) : ℝ)
      ≤ ∑ p ∈ Nat.primesLE y1, (p : ℝ) ^ (-(((lev ε p : ℕ) : ℤ) + 1)) := by
    rw [hbs_cast]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hpp : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hle : lev ε p ≤ yA y p := hyA p hpp.two_le
    have hexp : -(((yA y p : ℕ) : ℤ) + 1) ≤ -(((lev ε p : ℕ) : ℤ) + 1) := by
      have h2 : ((lev ε p : ℕ) : ℤ) ≤ ((yA y p : ℕ) : ℤ) := by exact_mod_cast hle
      linarith
    exact zpow_le_zpow_right₀ (by linarith) hexp
  have hy1le : y1 ≤ x0 := Nat.le_of_succ_le hy1
  have hsubA : Nat.primesLE y1 ⊆ caSupp ε := by
    intro p hp
    obtain ⟨hpy1, hpp⟩ := Nat.mem_primesLE.mp hp
    refine mem_caSupp.mpr ⟨hpp, ?_, hge0 p hpp (le_trans hpy1 hy1le)⟩
    by_contra hcon
    have hzero := lev_eq_zero_of_caB_le hε hpp.two_le (not_lt.mp hcon)
    have hone : 1 ≤ lev ε p := hge0 p hpp (le_trans hpy1 hy1le)
    exact absurd (hzero ▸ hone) (by omega)
  have hsubB : Nat.primesLE x0 \ Nat.primesLE y1 ⊆ caSupp ε := by
    intro p hp
    obtain ⟨hpx, _⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpx0, hpp⟩ := Nat.mem_primesLE.mp hpx
    refine mem_caSupp.mpr ⟨hpp, ?_, hge0 p hpp hpx0⟩
    by_contra hcon
    have hzero := lev_eq_zero_of_caB_le hε hpp.two_le (not_lt.mp hcon)
    have hone : 1 ≤ lev ε p := hge0 p hpp hpx0
    exact absurd (hzero ▸ hone) (by omega)
  have hU : (Nat.primesLE y1 ∪ (Nat.primesLE x0 \ Nat.primesLE y1)) ⊆ caSupp ε :=
    Finset.union_subset hsubA hsubB
  have hsubxy : Nat.primesLE y1 ⊆ Nat.primesLE x0 := by
    intro p hp
    obtain ⟨hpy1, hpp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨le_trans hpy1 hy1le, hpp⟩
  have hs : ((Sx : ℝ) - (Work.RHContract.RegionI.s2small y1 : ℝ))
      ≤ ∑ p ∈ Nat.primesLE x0 \ Nat.primesLE y1, (p : ℝ) ^ (-(((lev ε p : ℕ) : ℤ) + 1)) := by
    have hsplit : ∑ p ∈ Nat.primesLE x0 \ Nat.primesLE y1, (p : ℝ) ^ (-2 : ℤ)
        + ∑ p ∈ Nat.primesLE y1, (p : ℝ) ^ (-2 : ℤ)
        = ∑ p ∈ Nat.primesLE x0, (p : ℝ) ^ (-2 : ℤ) := Finset.sum_sdiff hsubxy
    have heq : ∑ p ∈ Nat.primesLE x0 \ Nat.primesLE y1, (p : ℝ) ^ (-2 : ℤ)
        = ∑ p ∈ Nat.primesLE x0 \ Nat.primesLE y1, (p : ℝ) ^ (-(((lev ε p : ℕ) : ℤ) + 1)) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      obtain ⟨hpx, hpny⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hpx0, hpp⟩ := Nat.mem_primesLE.mp hpx
      have hgt : y1 < p := by
        by_contra hcon
        exact hpny (Nat.mem_primesLE.mpr ⟨not_lt.mp hcon, hpp⟩)
      have hlev : lev ε p = 1 := le_antisymm (hlev1 p hgt) (hge0 p hpp hpx0)
      rw [hlev]
      norm_num
    have h2 : (Sx : ℝ) - (Work.RHContract.RegionI.s2small y1 : ℝ)
        ≤ ∑ p ∈ Nat.primesLE x0 \ Nat.primesLE y1, (p : ℝ) ^ (-2 : ℤ) := by
      rw [s2small_spec']
      linarith [hSx, hsplit]
    linarith [h2, heq.le]
  have hsum2 : (∑ p ∈ Nat.primesLE y1, (p : ℝ) ^ (-(((lev ε p : ℕ) : ℤ) + 1)))
      + (∑ p ∈ Nat.primesLE x0 \ Nat.primesLE y1,
          (p : ℝ) ^ (-(((lev ε p : ℕ) : ℤ) + 1)))
      ≤ ∑ p ∈ caSupp ε, (p : ℝ) ^ (-(((lev ε p : ℕ) : ℤ) + 1)) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hU (fun p _ _ => by positivity)
  linarith [hsum1, hsum2, hbs, hs]

/-! ## `log N_ε` dominates the `θ`-sum -/

private lemma sum_theta_le_log_caNumber (ε : ℝ) (hε : 0 < ε) (K : ℕ) (x : Fin K → ℕ)
    (hge : ∀ k : Fin K, ∀ p : ℕ, Nat.Prime p → p ≤ x k → k.val + 1 ≤ lev ε p) :
    ∑ k : Fin K, Chebyshev.theta ((x k : ℕ) : ℝ)
      ≤ Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ) := by
  have hsub : ∀ k : Fin K, Nat.primesLE (x k) ⊆ (Finset.range (caB ε)).filter Nat.Prime := by
    intro k p hp
    obtain ⟨hpx, hpp⟩ := Nat.mem_primesLE.mp hp
    have hlev : 1 ≤ lev ε p := le_trans (Nat.succ_pos k.val) (hge k p hpp hpx)
    have hB : p < caB ε := by
      by_contra hcon
      have := lev_eq_zero_of_caB_le hε hpp.two_le (not_lt.mp hcon)
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hB, hpp⟩
  have hstep : ∀ k : Fin K, Chebyshev.theta ((x k : ℕ) : ℝ)
      = ∑ p ∈ (Finset.range (caB ε)).filter Nat.Prime,
          (if p ∈ Nat.primesLE (x k) then Real.log (p : ℝ) else 0) := by
    intro k
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    rw [← Finset.sum_filter]
    congr 1
    ext p
    constructor
    · intro hp
      exact Finset.mem_filter.mpr ⟨hsub k hp, hp⟩
    · intro hp
      exact (Finset.mem_filter.mp hp).2
  have hcard : ∀ p ∈ (Finset.range (caB ε)).filter Nat.Prime,
      (Finset.univ.filter (fun k : Fin K => p ∈ Nat.primesLE (x k))).card ≤ lev ε p := by
    intro p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hc1 : (Finset.univ.filter (fun k : Fin K => p ∈ Nat.primesLE (x k))).card
        ≤ (Finset.univ.filter (fun k : Fin K => k.val + 1 ≤ lev ε p)).card := by
      refine Finset.card_le_card (fun k hk => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hge k p hpp (Nat.mem_primesLE.mp hk).1
    have hinj : Function.Injective (fun k : {k : Fin K // k.val + 1 ≤ lev ε p} =>
        (⟨k.val, Nat.lt_of_succ_le k.2⟩ : Fin (lev ε p))) := by
      intro a b hab
      simp only [Fin.mk.injEq] at hab
      exact Subtype.ext (Fin.ext hab)
    have hc2 := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin, Fintype.card_subtype] at hc2
    exact le_trans hc1 hc2
  calc ∑ k : Fin K, Chebyshev.theta ((x k : ℕ) : ℝ)
      = ∑ k : Fin K, ∑ p ∈ (Finset.range (caB ε)).filter Nat.Prime,
          (if p ∈ Nat.primesLE (x k) then Real.log (p : ℝ) else 0) :=
        Finset.sum_congr rfl (fun k _ => hstep k)
    _ = ∑ p ∈ (Finset.range (caB ε)).filter Nat.Prime, ∑ k : Fin K,
          (if p ∈ Nat.primesLE (x k) then Real.log (p : ℝ) else 0) := Finset.sum_comm
    _ = ∑ p ∈ (Finset.range (caB ε)).filter Nat.Prime,
          ((Finset.univ.filter (fun k : Fin K => p ∈ Nat.primesLE (x k))).card : ℝ)
            * Real.log (p : ℝ) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ (Finset.range (caB ε)).filter Nat.Prime, (lev ε p : ℝ) * Real.log (p : ℝ) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
        have hlog : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
        have hc : ((Finset.univ.filter (fun k : Fin K => p ∈ Nat.primesLE (x k))).card : ℝ)
            ≤ (lev ε p : ℝ) := by exact_mod_cast hcard p hp
        exact mul_le_mul_of_nonneg_right hc hlog
    _ = Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ) := (log_caNumber_eq_prod ε).symm


/-! ## The certificate -/

theorem blockCert
    (ε : ℝ) (hε : 0 < ε) (εT εB : ℚ) (hεT : ε ≤ (εT : ℝ)) (hεB : (εB : ℝ) < ε)
    (Kx Ky : ℕ) (hKx : 1 ≤ Kx) (hKy : 2 ≤ Ky)
    (hKtop : Work.RHContract.RegionI.Fhi 2 (Ky + 1) < εB)
    (x : Fin Kx → ℕ) (y : Fin Ky → ℕ) (θv : Fin Kx → ℚ)
    (hxle : ∀ k : Fin Kx, εT ≤ Work.RHContract.RegionI.Flo (x k) (k.val + 1))
    (hylo : ∀ k : Fin Ky, Work.RHContract.RegionI.Fhi (y k + 1) (k.val + 1) < εB)
    (hxlo : ∀ k : Fin Kx, 2 ≤ x k) (hxhi : ∀ k : Fin Kx, x k < 2 ^ 20)
    (hyhi : ∀ k : Fin Ky, y k + 1 < 2 ^ 20) (hy1k : ∀ k : Fin Ky, 1 ≤ y k)
    (hposy : ∀ k : Fin Ky, (0 : ℚ) < Work.RHContract.RegionI.logLowQ ((y k + 1 : ℕ) : ℚ))
    (hK1 : y ⟨1, by omega⟩ + 1 ≤ x ⟨0, by omega⟩)
    (hθv : ∀ k : Fin Kx, (θv k : ℝ) ≤ Chebyshev.theta (x k : ℝ))
    (LRu Sx : ℚ)
    (hLRu : Commons.NumberTheory.Mertens.logRatioSum ((y ⟨0, by omega⟩ : ℕ) : ℝ) ≤ (LRu : ℝ))
    (hSx : (Sx : ℝ) ≤ ∑ p ∈ Nat.primesLE (x ⟨0, by omega⟩), (p : ℝ) ^ (-2 : ℤ))
    (hT1 : (1 : ℚ) ≤ ∑ k, θv k) (hT2 : (∑ k, θv k) < 2 ^ 20)
    (hT3 : (1 : ℚ) ≤ Work.RHContract.RegionI.logLowQ (∑ k, θv k))
    (hT4 : Work.RHContract.RegionI.logLowQ (∑ k, θv k) < 2 ^ 20)
    (hmarg : LRu ≤ (57721 : ℚ) / 100000
              + Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, θv k))
              + (Sx - Work.RHContract.RegionI.s2small (y ⟨1, by omega⟩))
              + Work.RHContract.RegionI.bsmall y (y ⟨1, by omega⟩)) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hNpos : (0 : ℝ) < ((Work.RHPlan.caNumber ε : ℕ) : ℝ) := by
    exact_mod_cast caNumber_pos ε
  have hσpos : (0 : ℝ) < ((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ) := by
    have := ArithmeticFunction.sigma_pos 1 (Work.RHPlan.caNumber ε) (ne_of_gt (caNumber_pos ε))
    exact_mod_cast this
  -- level bounds
  have hlev_ge : ∀ k : Fin Kx, ∀ p : ℕ, Nat.Prime p → p ≤ x k → k.val + 1 ≤ lev ε p :=
    fun k p hpp hpx => lev_ge_of_le_x ε hε εT hεT Kx x hxle hxlo hxhi k hpp.two_le hpx
  have hlev_le : ∀ k : Fin Ky, ∀ p : ℕ, 2 ≤ p → y k < p → lev ε p ≤ k.val :=
    fun k p hp hpy => lev_le_of_gt_y ε hε εB hεB Ky y hylo hyhi hy1k hposy k hp hpy
  have hlevK : ∀ p : ℕ, 2 ≤ p → lev ε p ≤ Ky := fun p hp => lev_le_K ε hε εB hεB Ky hKy hKtop hp
  have hyc := cF_lt_of_Fhi_lt ε εB hεB Ky y hylo hyhi hy1k hposy
  have hdecomp := log_sigma_div_eq ε hε
  -- Mertens part
  have hM : (∑ p ∈ caSupp ε, Real.log ((p : ℝ) / ((p : ℝ) - 1))) ≤ (LRu : ℝ) := by
    refine le_trans (mertens_le hε (y ⟨0, by omega⟩) ?_) hLRu
    intro p hpp hlev
    by_contra hcon
    have h1 := hlev_le ⟨0, by omega⟩ p hpp.two_le (lt_of_not_ge hcon)
    simp only [Fin.val_zero] at h1
    omega
  -- correction part
  have hC := corr_le (ε := ε) hε Ky hKy y (x ⟨0, by omega⟩) (y ⟨1, by omega⟩)
    rfl hK1 (by have := hy1k ⟨1, by omega⟩; omega)
    (fun p hpp hpx => hlev_ge ⟨0, by omega⟩ p hpp hpx)
    (fun p hp2 => lev_le_yA hε Ky y hy1k hyc hlevK hp2)
    (fun p hlt => hlev_le ⟨1, by omega⟩ p (by have := hy1k ⟨1, by omega⟩; omega) hlt)
    Sx hSx
  -- `log N_ε ≥ Σ_k θv k`
  have hT : ((∑ k, θv k : ℚ) : ℝ) ≤ Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ) := by
    have h1 : ((∑ k, θv k : ℚ) : ℝ) ≤ ∑ k : Fin Kx, Chebyshev.theta ((x k : ℕ) : ℝ) := by
      rw [Rat.cast_sum]
      exact Finset.sum_le_sum (fun k _ => hθv k)
    have h2 := sum_theta_le_log_caNumber ε hε Kx x (fun k p hpp hpx => hlev_ge k p hpp hpx)
    linarith
  have hT1R : (1 : ℝ) ≤ ((∑ k, θv k : ℚ) : ℝ) := by exact_mod_cast hT1
  have hT2R : ((∑ k, θv k : ℚ) : ℝ) < 2 ^ 20 := by exact_mod_cast hT2
  have hT3R : (1 : ℝ) ≤ (Work.RHContract.RegionI.logLowQ (∑ k, θv k) : ℝ) := by
    exact_mod_cast hT3
  have hT4R : (Work.RHContract.RegionI.logLowQ (∑ k, θv k) : ℝ) < 2 ^ 20 := by
    exact_mod_cast hT4
  have hlogT : (1 : ℝ) ≤ Real.log ((∑ k, θv k : ℚ) : ℝ) :=
    le_trans hT3R (logLowQ_le' hT1 hT2)
  have hTpos : 0 < ((∑ k, θv k : ℚ) : ℝ) := lt_of_lt_of_le one_pos hT1R
  have hTgt : 1 < ((∑ k, θv k : ℚ) : ℝ) := by
    have h := Real.exp_le_exp.mpr hlogT
    rw [Real.exp_log hTpos] at h
    linarith [Real.exp_one_gt_two, h]
  have hlogN1 : 1 < Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ) := lt_of_lt_of_le hTgt hT
  have hloglogN : 0 < Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)) :=
    Real.log_pos hlogN1
  have hL2 : (Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, θv k)) : ℝ)
      ≤ Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ))) := by
    have h1 : (Work.RHContract.RegionI.logLowQ (∑ k, θv k) : ℝ)
        ≤ Real.log ((∑ k, θv k : ℚ) : ℝ) := logLowQ_le' hT1 hT2
    have h2 : Real.log ((∑ k, θv k : ℚ) : ℝ)
        ≤ Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)) := Real.log_le_log hTpos hT
    have h2' : Real.log (Real.log ((∑ k, θv k : ℚ) : ℝ))
        ≤ Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ))) :=
      Real.log_le_log (Real.log_pos hTgt) h2
    have h3 : Real.log ((Work.RHContract.RegionI.logLowQ (∑ k, θv k) : ℚ) : ℝ)
        ≤ Real.log (Real.log ((∑ k, θv k : ℚ) : ℝ)) := Real.log_le_log (lt_of_lt_of_le one_pos hT3R) h1
    have h4 : (Work.RHContract.RegionI.logLowQ
          (Work.RHContract.RegionI.logLowQ (∑ k, θv k)) : ℝ)
        ≤ Real.log ((Work.RHContract.RegionI.logLowQ (∑ k, θv k) : ℚ) : ℝ) :=
      logLowQ_le' hT3 hT4
    linarith [h4, h3, h2']
  have hmargR : (LRu : ℝ) ≤ (57721 : ℝ) / 100000
      + (Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, θv k)) : ℝ)
      + ((Sx : ℝ) - (Work.RHContract.RegionI.s2small (y ⟨1, by omega⟩) : ℝ))
      + (Work.RHContract.RegionI.bsmall y (y ⟨1, by omega⟩) : ℝ) := by
    have h := ratCast_le_real hmarg
    push_cast at h
    exact h
  have hlogσ : Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)
        / ((Work.RHPlan.caNumber ε : ℕ) : ℝ))
      ≤ (57721 : ℝ) / 100000
        + (Work.RHContract.RegionI.logLowQ (Work.RHContract.RegionI.logLowQ (∑ k, θv k)) : ℝ) := by
    rw [hdecomp]
    linarith
  have hfin : Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)
        / ((Work.RHPlan.caNumber ε : ℕ) : ℝ))
      < Real.eulerMascheroniConstant
        + Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ))) := by
    have hγ := gamma_gt_57721
    linarith
  rw [Work.RHPlan.RobinBound]
  have hratio : 0 < ((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)
      / ((Work.RHPlan.caNumber ε : ℕ) : ℝ) := div_pos hσpos hNpos
  have hexp : ((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)
        / ((Work.RHPlan.caNumber ε : ℕ) : ℝ)
      ≤ Real.exp (Real.eulerMascheroniConstant
        + Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)))) :=
    (Real.log_le_iff_le_exp hratio).mp hfin.le
  rw [Real.exp_add, Real.exp_log hloglogN] at hexp
  calc ((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)
      ≤ (Real.exp Real.eulerMascheroniConstant
          * Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)))
          * ((Work.RHPlan.caNumber ε : ℕ) : ℝ) := (div_le_iff₀ hNpos).mp hexp
    _ = Real.exp Real.eulerMascheroniConstant * ((Work.RHPlan.caNumber ε : ℕ) : ℝ)
          * Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)) := by ring


end

end Work.RHContract.A.RegionI
