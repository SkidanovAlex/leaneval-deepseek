import Mathlib
import Submission.Work.RHContract.A.RegionI.Defs
import Submission.Work.RHContract.A.RegionI.altLog_bounds
import Submission.Work.RHContract.A.RegionI.steps_basic

/-!
# Region I: the level-function core

The Nicolas level function `cF p k` controls the exponent of `p` in the colossally abundant
number `N_ε`:  `k ≤ ⌊caMu p ε⌋₊ ↔ ε ≤ cF p k` (`caMu_ge_iff_cF` below).  Consequently a
prime `p ≤ x` with `ε ≤ cF x k` lies in level `k`, and a prime `p > y` with
`cF (y+1) k < ε` does not — which is all the structure the region-I certificates use.
-/

open scoped BigOperators
open Finset

namespace Work.RHContract.RegionI

noncomputable section

/-! ## `θ` over consecutive primes -/

theorem theta_step {m n : ℕ} (hm : m < n) (hn : Nat.Prime n)
    (hgap : ∀ p, m < p → p < n → ¬ Nat.Prime p) :
    Chebyshev.theta (n : ℝ) = Chebyshev.theta (m : ℝ) + Real.log (n : ℝ) := by
  have hset : Nat.primesLE n = insert n (Nat.primesLE m) := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_insert]
    constructor
    · rintro ⟨hpn, hp⟩
      rcases eq_or_lt_of_le hpn with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨le_of_not_gt (fun h => hgap p h hlt hp), hp⟩
    · rintro (rfl | ⟨hpm, hp⟩)
      · exact ⟨le_rfl, hn⟩
      · exact ⟨le_trans hpm (le_of_lt hm), hp⟩
  have hnot : n ∉ Nat.primesLE m := by
    intro hcon
    rw [Nat.mem_primesLE] at hcon
    omega
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log, hset,
    Finset.sum_insert hnot]
  ring

/-! ## `S_k` and the level function -/

lemma caS_eq (p k : ℕ) :
    (caS p k : ℚ) = (p : ℚ) * ∑ i ∈ Finset.range k, (p : ℚ) ^ i := by
  have h1 : (caS p k : ℚ) = ∑ i ∈ Finset.range k, (p : ℚ) ^ (i + 1) := by
    unfold caS
    push_cast
    rfl
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [pow_succ]
  ring

lemma caS_mul_sub_one (p k : ℕ) :
    (caS p k : ℚ) * ((p : ℚ) - 1) = (p : ℚ) ^ (k + 1) - (p : ℚ) := by
  rw [caS_eq, mul_assoc, geom_sum_mul]
  ring

lemma caS_pos_nat {p k : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) : 1 ≤ caS p k := by
  unfold caS
  have hmem : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have h := Finset.single_le_sum (f := fun i : ℕ => p ^ (i + 1))
    (fun i _ => Nat.zero_le _) hmem
  have h' : p ≤ caS p k := by simpa [caS] using h
  exact le_trans hp h'

lemma caS_lt_nat {p q k : ℕ} (hk : 1 ≤ k) (h : p < q) : caS p k < caS q k := by
  unfold caS
  refine Finset.sum_lt_sum (fun i _ => Nat.pow_le_pow_left (le_of_lt h) (i + 1)) ?_
  exact ⟨0, Finset.mem_range.mpr (by omega), by simpa using h⟩

/-- `(p^{k+1}−1)/(p^{k+1}−p) = 1 + 1/S_k(p)`: the `S_k` form of the level function. -/
lemma ratio_eq_one_add_inv_caS {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (((p : ℝ) ^ (k + 1) - 1) / ((p : ℝ) ^ (k + 1) - (p : ℝ))) = 1 + 1 / (caS p k : ℝ) := by
  have hQ := caS_mul_sub_one p k
  have hR : (caS p k : ℝ) * ((p : ℝ) - 1) = (p : ℝ) ^ (k + 1) - (p : ℝ) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) hQ
    push_cast at h
    exact h
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hS1 : (1 : ℝ) ≤ (caS p k : ℝ) := by
    exact_mod_cast caS_pos_nat (by omega : 1 ≤ p) hk
  have hSpos : (0 : ℝ) < (caS p k : ℝ) := lt_of_lt_of_le one_pos hS1
  have hden : (p : ℝ) ^ (k + 1) - (p : ℝ) ≠ 0 := by
    have hlt : (0 : ℝ) < (p : ℝ) ^ (k + 1) - (p : ℝ) := by
      rw [← hR]
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    linarith
  have hmain : (p : ℝ) ^ (k + 1) - 1 =
      (1 + 1 / (caS p k : ℝ)) * ((p : ℝ) ^ (k + 1) - (p : ℝ)) := by
    field_simp
    nlinarith [hR]
  exact (div_eq_iff hden).mpr hmain

lemma cF_eq_log {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    cF p k = Real.log (1 + 1 / (caS p k : ℝ)) / Real.log (p : ℝ) := by
  unfold cF
  rw [ratio_eq_one_add_inv_caS hp hk]

/-- `F(·,k)` is strictly decreasing in `p` (for `p ≥ 2`, `k ≥ 1`). -/
lemma cF_anti {p q k : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 1 ≤ k) (h : p < q) :
    cF q k < cF p k := by
  have hp1 : (1 : ℕ) < p := by omega
  have hq1 : (1 : ℕ) < q := by omega
  rw [cF_eq_log hq hk, cF_eq_log hp hk]
  have hS : (caS p k : ℝ) < (caS q k : ℝ) := by
    exact_mod_cast caS_lt_nat hk h
  have hSpos : (0 : ℝ) < (caS p k : ℝ) := by
    have : 1 ≤ caS p k := caS_pos_nat (by omega) hk
    exact_mod_cast (by omega : 0 < caS p k)
  have hqpos : (0 : ℝ) < (caS q k : ℝ) := by
    have : 1 ≤ caS q k := caS_pos_nat (by omega) hk
    exact_mod_cast (by omega : 0 < caS q k)
  have hA : Real.log (1 + 1 / (caS q k : ℝ)) < Real.log (1 + 1 / (caS p k : ℝ)) := by
    refine Real.log_lt_log (by positivity) ?_
    have h' : 1 / (caS p k : ℝ) > 1 / (caS q k : ℝ) := one_div_lt_one_div_of_lt hSpos hS
    linarith
  have hApos : (0 : ℝ) < Real.log (1 + 1 / (caS q k : ℝ)) := by
    refine Real.log_pos ?_
    have : (0 : ℝ) < 1 / (caS q k : ℝ) := by positivity
    linarith
  have hLp : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp1)
  have hLq : (0 : ℝ) < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hLpq : Real.log (p : ℝ) < Real.log (q : ℝ) :=
    Real.log_lt_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast h)
  rw [div_lt_div_iff₀ hLq hLp]
  nlinarith [hA, hApos, hLpq, hLq]

/-! ## The level criterion -/

theorem caMu_ge_iff_cF {p : ℕ} {ε : ℝ} {k : ℕ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k) :
    (k : ℝ) ≤ Work.RHPlan.caMu p ε ↔ ε ≤ cF p k := by
  simpa [Work.RHPlan.caMu, cF] using
    (Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε k hp hε hk)

/-- Every prime `p ≤ x` with `ε ≤ cF x k` is in level `k`. -/
theorem level_ge {ε : ℝ} (hε : 0 < ε) {p x k : ℕ} (hp : 2 ≤ p) (hx : 2 ≤ x) (hk : 1 ≤ k)
    (hpx : p ≤ x) (h : ε ≤ cF x k) : k ≤ ⌊Work.RHPlan.caMu p ε⌋₊ := by
  have hmono : cF x k ≤ cF p k := by
    rcases eq_or_lt_of_le hpx with rfl | hlt
    · exact le_rfl
    · exact le_of_lt (cF_anti hp hx hk hlt)
  exact Nat.le_floor ((caMu_ge_iff_cF hp hε hk).mpr (le_trans h hmono))

/-- Every prime `p > y` with `cF (y+1) k < ε` is *not* in level `k`. -/
theorem level_lt {ε : ℝ} (hε : 0 < ε) {p y k : ℕ} (hp : 2 ≤ p) (hy : 1 ≤ y) (hk : 1 ≤ k)
    (hpy : y < p) (h : cF (y + 1) k < ε) : ⌊Work.RHPlan.caMu p ε⌋₊ < k := by
  have hy2 : 2 ≤ y + 1 := by omega
  have hmono : cF p k ≤ cF (y + 1) k := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpy) with hh | hlt
    · exact le_of_eq (by rw [← hh])
    · exact le_of_lt (cF_anti hy2 hp hk hlt)
  by_contra hcon
  rw [not_lt] at hcon
  have hge : (k : ℝ) ≤ Work.RHPlan.caMu p ε :=
    le_trans (by exact_mod_cast hcon) (Nat.floor_le (le_of_lt (Commons.NumberTheory.Robin.caMu_pos (by omega : 2 ≤ p) hε)))
  have := (caMu_ge_iff_cF hp hε hk).mp hge
  linarith [hmono]

end

end Work.RHContract.RegionI

namespace Work.RHContract.RegionI

noncomputable section

open scoped BigOperators
open Finset

/-! ## Rational bounds for the level function -/

lemma cFr_cast (p k : ℕ) :
    ((cFr p k : ℚ) : ℝ) = ((p : ℝ) ^ (k + 1) - 1) / ((p : ℝ) ^ (k + 1) - (p : ℝ)) := by
  unfold cFr
  push_cast
  rfl

lemma cFr_eq {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) : cFr p k = 1 + 1 / (caS p k : ℚ) := by
  apply Rat.cast_injective (α := ℝ)
  rw [cFr_cast]
  push_cast
  rw [ratio_eq_one_add_inv_caS hp hk]

lemma one_le_cFr {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) : (1 : ℚ) ≤ cFr p k := by
  rw [cFr_eq hp hk]
  have h : (1 : ℚ) ≤ (caS p k : ℚ) := by exact_mod_cast caS_pos_nat (by omega) hk
  have : (0 : ℚ) < (caS p k : ℚ) := lt_of_lt_of_le one_pos h
  have h2 : (0 : ℚ) ≤ 1 / (caS p k : ℚ) := by positivity
  linarith

lemma cFr_le_two {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) : cFr p k ≤ 2 := by
  rw [cFr_eq hp hk]
  have h : (1 : ℚ) ≤ (caS p k : ℚ) := by exact_mod_cast caS_pos_nat (by omega) hk
  have hpos : (0 : ℚ) < (caS p k : ℚ) := lt_of_lt_of_le one_pos h
  have : 1 / (caS p k : ℚ) ≤ 1 := by
    rw [div_le_one hpos]; exact h
  linarith

lemma altLog_cast (t : ℚ) (N : ℕ) :
    ((altLog t N : ℚ) : ℝ)
      = ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * (t : ℝ) ^ (i + 1) / ((i + 1 : ℕ) : ℝ) := by
  unfold altLog
  push_cast
  rfl

lemma log2LoQ_le : ((log2LoQ : ℚ) : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  have h2 : ((log2LoQ : ℚ) : ℝ) ≤ (6931471803 : ℝ) / 10 ^ 10 := by
    rw [log2LoQ]; norm_num
  linarith

lemma log2UpQ_ge : Real.log 2 ≤ ((log2UpQ : ℚ) : ℝ) := by
  have h := Real.log_two_lt_d9
  have h2 : (6931471809 : ℝ) / 10 ^ 10 ≤ ((log2UpQ : ℚ) : ℝ) := by
    rw [log2UpQ]; norm_num
  linarith

lemma log1pLo_le {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (log1pLo t : ℝ) ≤ Real.log (1 + (t : ℝ)) := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Rat.cast_nonneg.mpr h0
  unfold log1pLo
  by_cases hA : t ≤ 1 / 1024
  · rw [if_pos hA, altLog_cast]
    have hc : (t : ℝ) ≤ 1 / 2 := by
      have h' := Rat.cast_le (K := ℝ).mpr hA; norm_num at h'; linarith
    exact (Work.RHContract.A.RegionI.altLog_bounds ht hc 4).1 (by norm_num)
  · rw [if_neg hA]
    by_cases hB : t ≤ 1 / 32
    · rw [if_pos hB, altLog_cast]
      have hc : (t : ℝ) ≤ 1 / 2 := by
        have h' := Rat.cast_le (K := ℝ).mpr hB; norm_num at h'; linarith
      exact (Work.RHContract.A.RegionI.altLog_bounds ht hc 10).1 (by norm_num)
    · rw [if_neg hB]
      by_cases hC : t ≤ 1 / 2
      · rw [if_pos hC, altLog_cast]
        have hc : (t : ℝ) ≤ 1 / 2 := by
          have h' := Rat.cast_le (K := ℝ).mpr hC; norm_num at h'; linarith
        exact (Work.RHContract.A.RegionI.altLog_bounds ht hc 46).1 (by norm_num)
      · rw [if_neg hC]
        exact Commons.NumberTheory.Robin.RobinCaFval.logOneAddLower_le_log_one_add t h0

lemma le_log1pUp {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.log (1 + (t : ℝ)) ≤ (log1pUp t : ℝ) := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Rat.cast_nonneg.mpr h0
  unfold log1pUp
  by_cases hA : t ≤ 1 / 1024
  · rw [if_pos hA, altLog_cast]
    have hc : (t : ℝ) ≤ 1 / 2 := by
      have h' := Rat.cast_le (K := ℝ).mpr hA; norm_num at h'; linarith
    exact (Work.RHContract.A.RegionI.altLog_bounds ht hc 5).2 (by norm_num)
  · rw [if_neg hA]
    by_cases hB : t ≤ 1 / 32
    · rw [if_pos hB, altLog_cast]
      have hc : (t : ℝ) ≤ 1 / 2 := by
        have h' := Rat.cast_le (K := ℝ).mpr hB; norm_num at h'; linarith
      exact (Work.RHContract.A.RegionI.altLog_bounds ht hc 11).2 (by norm_num)
    · rw [if_neg hB]
      by_cases hC : t ≤ 1 / 2
      · rw [if_pos hC, altLog_cast]
        have hc : (t : ℝ) ≤ 1 / 2 := by
          have h' := Rat.cast_le (K := ℝ).mpr hC; norm_num at h'; linarith
        exact (Work.RHContract.A.RegionI.altLog_bounds ht hc 47).2 (by norm_num)
      · rw [if_neg hC]
        exact Commons.NumberTheory.Robin.RobinCaFval.logOneAddUpper_ge_log_one_add t h0

lemma logLowAuxQ_le (k : ℕ) (x : ℚ) (h1 : 1 ≤ x) (h2 : x < 2 ^ k) :
    (logLowAuxQ x k : ℝ) ≤ Real.log (x : ℝ) := by
  induction k generalizing x with
  | zero =>
      have : (x : ℚ) < 1 := by simpa using h2
      linarith
  | succ k ih =>
      by_cases hx : x < 2
      · rw [logLowAuxQ, if_pos hx]
        have h0 : (0 : ℚ) ≤ x - 1 := by linarith
        have hlt : x - 1 ≤ 1 := by linarith
        have h := log1pLo_le h0 hlt
        have hxr : (1 : ℝ) + ((x - 1 : ℚ) : ℝ) = (x : ℝ) := by push_cast; ring
        rwa [hxr] at h
      · rw [logLowAuxQ, if_neg hx]
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
        linarith [log2LoQ_le, hih]

lemma logUpAuxQ_ge (k : ℕ) (x : ℚ) (h1 : 1 ≤ x) (h2 : x < 2 ^ k) :
    Real.log (x : ℝ) ≤ (logUpAuxQ x k : ℝ) := by
  induction k generalizing x with
  | zero =>
      have : (x : ℚ) < 1 := by simpa using h2
      linarith
  | succ k ih =>
      by_cases hx : x < 2
      · rw [logUpAuxQ, if_pos hx]
        have h0 : (0 : ℚ) ≤ x - 1 := by linarith
        have hlt : x - 1 ≤ 1 := by linarith
        have h := le_log1pUp h0 hlt
        have hxr : (1 : ℝ) + ((x - 1 : ℚ) : ℝ) = (x : ℝ) := by push_cast; ring
        rwa [hxr] at h
      · rw [logUpAuxQ, if_neg hx]
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
        linarith [log2UpQ_ge, hih]

lemma logLowQ_le {x : ℚ} (h1 : 1 ≤ x) (h2 : x < 2 ^ 20) :
    (logLowQ x : ℝ) ≤ Real.log (x : ℝ) :=
  logLowAuxQ_le 26 x h1 (by norm_num at h2 ⊢; linarith)

lemma le_logUpQ {x : ℚ} (h1 : 1 ≤ x) (h2 : x < 2 ^ 20) :
    Real.log (x : ℝ) ≤ (logUpQ x : ℝ) :=
  logUpAuxQ_ge 26 x h1 (by norm_num at h2 ⊢; linarith)

/-- The certified rational lower bound for `F(p,k)`. -/
theorem Flo_le_cF {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) (hpb : p < 2 ^ 20) :
    (Flo p k : ℝ) ≤ cF p k := by
  have h1 : (1 : ℚ) ≤ cFr p k := one_le_cFr hp hk
  have h2 : cFr p k < 2 ^ 20 := lt_of_le_of_lt (cFr_le_two hp hk) (by norm_num)
  have h3 : (logLowQ (cFr p k) : ℝ) ≤ Real.log (((cFr p k : ℚ) : ℝ)) := logLowQ_le h1 h2
  have h4 : Real.log ((p : ℚ) : ℝ) ≤ (logUpQ (p : ℚ) : ℝ) :=
    le_logUpQ (by exact_mod_cast (by omega : 1 ≤ p)) (by exact_mod_cast hpb)
  have hLp : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hUp : (0 : ℝ) < (logUpQ (p : ℚ) : ℝ) := lt_of_lt_of_le hLp h4
  have hA : (0 : ℝ) ≤ Real.log (((cFr p k : ℚ) : ℝ)) := Real.log_nonneg (by exact_mod_cast h1)
  calc (Flo p k : ℝ) = (logLowQ (cFr p k) : ℝ) / (logUpQ (p : ℚ) : ℝ) := by
        simp only [Flo, Rat.cast_div]
    _ ≤ Real.log (((cFr p k : ℚ) : ℝ)) / (logUpQ (p : ℚ) : ℝ) :=
        div_le_div_of_nonneg_right h3 (le_of_lt hUp)
    _ ≤ Real.log (((cFr p k : ℚ) : ℝ)) / Real.log (p : ℝ) :=
        div_le_div_of_nonneg_left hA hLp h4
    _ = cF p k := by rw [cF, cFr_cast]

/-- The certified rational upper bound for `F(p,k)`. -/
theorem cF_le_Fhi {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) (hpb : p < 2 ^ 20)
    (hpos : (0 : ℚ) < logLowQ (p : ℚ)) :
    cF p k ≤ (Fhi p k : ℝ) := by
  have h1 : (1 : ℚ) ≤ cFr p k := one_le_cFr hp hk
  have h2 : cFr p k < 2 ^ 20 := lt_of_le_of_lt (cFr_le_two hp hk) (by norm_num)
  have h3 : Real.log (((cFr p k : ℚ) : ℝ)) ≤ (logUpQ (cFr p k) : ℝ) := le_logUpQ h1 h2
  have h4 : (logLowQ (p : ℚ) : ℝ) ≤ Real.log (p : ℝ) :=
    logLowQ_le (by exact_mod_cast (by omega : 1 ≤ p)) (by exact_mod_cast hpb)
  have h5 : (0 : ℝ) < (logLowQ (p : ℚ) : ℝ) := by exact_mod_cast hpos
  have hLp : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hA : (0 : ℝ) ≤ Real.log (((cFr p k : ℚ) : ℝ)) := Real.log_nonneg (by exact_mod_cast h1)
  calc cF p k = Real.log (((cFr p k : ℚ) : ℝ)) / Real.log (p : ℝ) := by rw [cF, cFr_cast]
    _ ≤ Real.log (((cFr p k : ℚ) : ℝ)) / (logLowQ (p : ℚ) : ℝ) :=
        div_le_div_of_nonneg_left hA h5 h4
    _ ≤ (logUpQ (cFr p k) : ℝ) / (logLowQ (p : ℚ) : ℝ) :=
        div_le_div_of_nonneg_right h3 (le_of_lt h5)
    _ = (Fhi p k : ℝ) := by simp only [Fhi, Rat.cast_div]

end

end Work.RHContract.RegionI

namespace Work.RHContract.RegionI

noncomputable section

open scoped BigOperators
open Finset

lemma cast_rational_le {a b : ℚ} (h : a ≤ b) : ((a : ℚ) : ℝ) ≤ ((b : ℚ) : ℝ) :=
  Rat.cast_le.mpr h

lemma smallP_toFinset (N : ℕ) : (smallP N).toFinset = Nat.primesLE N := by
  ext p
  simp only [List.mem_toFinset, smallP, List.mem_filter, List.mem_range, Nat.mem_primesLE,
    isP_iff, Nat.lt_succ_iff]

lemma smallP_nodup (N : ℕ) : (smallP N).Nodup := by
  unfold smallP
  exact List.Nodup.filter _ (List.nodup_range)

lemma s2small_spec (N : ℕ) :
    (s2small N : ℝ) = ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-2 : ℤ) := by
  unfold s2small
  rw [smallP_toFinset]
  push_cast
  ring

end

end Work.RHContract.RegionI
