import Mathlib
import Mathlib.NumberTheory.PrimeCounting
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto

open Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

/-! # A Mertens-type product over odd primes

We prove that `log z * ∏_{3 ≤ p ≤ z} (1 − 1/(p−1))` has a positive limit as
`z → ∞`.  The proof:

* writes the log of the product as a sum of `log (1 − 1/(p−1))`;
* uses the identity `log (1 − 1/(p−1)) = log (1 − 1/(p−1)^2) − log (p/(p−1))`
  (valid for odd primes `p`);
* the `log (p/(p−1))` part is governed by Mertens' third theorem
  (`sum_log_prime_ratio_real_tendsto`), while
* the `log (1 − 1/(p−1)^2)` correction is summable over the primes (its
  partial sums converge, `ppSqCorr_partial_tendsto`).

This yields convergence of `log (log z) + Σ log (1 − 1/(p−1))`, and
exponentiating gives the statement. -/

/-- correction term: `log (1 - 1/(p-1)^2)` on primes, `0` elsewhere.
At `p = 2` the argument is `0` and `Real.log 0 = 0`. -/
private def ppSqCorr (p : ℕ) : ℝ := if Nat.Prime p then Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2) else 0

private lemma ppSqCorr_eq_zero_of_not_prime {p : ℕ} (hp : ¬ Nat.Prime p) : ppSqCorr p = 0 := by
  simp [ppSqCorr, hp]

private lemma ppSqCorr_eq_two : ppSqCorr 2 = 0 := by
  simp [ppSqCorr]
  norm_num

private lemma two_lt_of_prime_ne_two {p : ℕ} (hp : Nat.Prime p) (h : p ≠ 2) : 3 ≤ p := by
  have hp2 : 2 ≤ p := Nat.Prime.two_le hp
  omega

private lemma sq_ge_four_of_two_le {x : ℝ} (hx : 2 ≤ x) : (4 : ℝ) ≤ x ^ 2 := by
  nlinarith [sq_nonneg (x - 2)]

private lemma inv_sq_lt_one_of_two_le {x : ℝ} (hx : 2 ≤ x) : 1 / x ^ 2 < 1 := by
  have hx0 : 0 < x := by linarith
  have hsq : (1 : ℝ) ≤ x ^ 2 := by
    have h4 : (4 : ℝ) ≤ x ^ 2 := sq_ge_four_of_two_le hx
    linarith
  rw [div_lt_iff₀ (by positivity : 0 < x ^ 2)]
  nlinarith

/-- `1 - 1/(p-1)^2` is positive for `3 ≤ p`. -/
private lemma ppSqCorr_arg_pos {p : ℕ} (hp : 3 ≤ p) : 0 < 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpm1 : (2 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hlt : 1 / ((p : ℝ) - 1) ^ 2 < 1 := inv_sq_lt_one_of_two_le hpm1
  linarith

private lemma ppSqCorr_arg_ne_zero {p : ℕ} (hp : 3 ≤ p) : (1 - 1 / ((p : ℝ) - 1) ^ 2) ≠ 0 := by
  exact ne_of_gt (ppSqCorr_arg_pos hp)

private lemma ppSqCorr_arg_le_one {p : ℕ} (_hp : 3 ≤ p) : 1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
  have h : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
  linarith

private lemma ppSqCorr_log_nonpos {p : ℕ} (hp : 3 ≤ p) :
    Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ 0 := by
  have hle : Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ Real.log 1 :=
    Real.log_le_log (ppSqCorr_arg_pos hp) (ppSqCorr_arg_le_one hp)
  simpa using hle

private lemma ppSqCorr_abs_eq {n : ℕ} (hn : 3 ≤ n) :
    |Real.log (1 - 1 / ((n : ℝ) - 1) ^ 2)| = -Real.log (1 - 1 / ((n : ℝ) - 1) ^ 2) := by
  exact abs_of_nonpos (ppSqCorr_log_nonpos hn)

private lemma ppSqCorr_neg_log {n : ℕ} (hn : 3 ≤ n) :
    -Real.log (1 - 1 / ((n : ℝ) - 1) ^ 2) =
      Real.log (((n : ℝ) - 1) ^ 2 / (((n : ℝ) - 1) ^ 2 - 1)) := by
  have harg_ne : (1 - 1 / ((n : ℝ) - 1) ^ 2) ≠ 0 := ppSqCorr_arg_ne_zero hn
  rw [← Real.log_inv]
  congr 1
  have hm1 : ((n : ℝ) - 1) ≠ 0 := by
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hden : ((n : ℝ) - 1) ^ 2 - 1 ≠ 0 := by
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hge : (2 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    have hsq : (4 : ℝ) ≤ ((n : ℝ) - 1) ^ 2 := sq_ge_four_of_two_le hge
    linarith
  field_simp [hm1, hden]

private lemma log_one_add_le {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u := by
  have hpos : 0 < 1 + u := by linarith
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

private lemma ppSqCorr_abs_le_two_div_sq {n : ℕ} (hn : 3 ≤ n) :
    |Real.log (1 - 1 / ((n : ℝ) - 1) ^ 2)| ≤ 2 / ((n : ℝ) - 1) ^ 2 := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hge2 : (2 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hden_pos : 0 < ((n : ℝ) - 1) ^ 2 - 1 := by
    have hsq : (4 : ℝ) ≤ ((n : ℝ) - 1) ^ 2 := sq_ge_four_of_two_le hge2
    linarith
  have hden_ne : ((n : ℝ) - 1) ^ 2 - 1 ≠ 0 := ne_of_gt hden_pos
  have harg : (1 - 1 / ((n : ℝ) - 1) ^ 2) ≠ 0 := ppSqCorr_arg_ne_zero hn
  have hposarg : 0 < 1 - 1 / ((n : ℝ) - 1) ^ 2 := ppSqCorr_arg_pos hn
  calc
    |Real.log (1 - 1 / ((n : ℝ) - 1) ^ 2)|
        = -Real.log (1 - 1 / ((n : ℝ) - 1) ^ 2) := ppSqCorr_abs_eq hn
    _ = Real.log (((n : ℝ) - 1) ^ 2 / (((n : ℝ) - 1) ^ 2 - 1)) := ppSqCorr_neg_log hn
    _ = Real.log (1 + 1 / (((n : ℝ) - 1) ^ 2 - 1)) := by
        congr 1
        field_simp [hden_ne]
        ring
    _ ≤ 1 / (((n : ℝ) - 1) ^ 2 - 1) := log_one_add_le (le_of_lt (one_div_pos.mpr hden_pos))
    _ ≤ 2 / ((n : ℝ) - 1) ^ 2 := by
        have hsq : (4 : ℝ) ≤ ((n : ℝ) - 1) ^ 2 := sq_ge_four_of_two_le hge2
        have hpos : 0 < ((n : ℝ) - 1) ^ 2 := by positivity
        rw [div_le_div_iff₀ hden_pos hpos]
        nlinarith

/-- final bound over all naturals against `C / n^2`. -/
private lemma ppSqCorr_ext_bound (n : ℕ) : ‖ppSqCorr n‖ ≤ (8 : ℝ) / (n : ℝ) ^ 2 := by
  by_cases hp : Nat.Prime n
  · by_cases hn2 : n = 2
    · subst hn2
      rw [ppSqCorr_eq_two]
      simp
      exact div_nonneg (by norm_num) (sq_nonneg ((2 : ℝ)))
    · have hn3 : 3 ≤ n := two_lt_of_prime_ne_two hp hn2
      have hle1 : |Real.log (1 - 1 / ((n : ℝ) - 1) ^ 2)| ≤ 2 / ((n : ℝ) - 1) ^ 2 :=
        ppSqCorr_abs_le_two_div_sq hn3
      have hle2 : 2 / ((n : ℝ) - 1) ^ 2 ≤ (8 : ℝ) / (n : ℝ) ^ 2 := by
        have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
        have hge2 : (2 : ℝ) ≤ (n : ℝ) - 1 := by linarith
        have hposm1 : 0 < (n : ℝ) - 1 := by linarith
        have hposn : 0 < (n : ℝ) := by linarith
        have hposm1sq : 0 < ((n : ℝ) - 1) ^ 2 := by positivity
        have hposnsq : 0 < (n : ℝ) ^ 2 := by positivity
        rw [div_le_div_iff₀ hposm1sq hposnsq]
        nlinarith
      rw [ppSqCorr, if_pos hp]
      simpa [Real.norm_eq_abs] using le_trans hle1 hle2
  · rw [ppSqCorr_eq_zero_of_not_prime hp]
    simp
    exact div_nonneg (by norm_num) (sq_nonneg (n : ℝ))

private lemma summable_ppSqCorr : Summable ppSqCorr := by
  refine Summable.of_norm_bounded ?_ ppSqCorr_ext_bound
  have h₁ : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have h₂ : Summable (fun n : ℕ => (8 : ℝ) * (1 / (n : ℝ) ^ 2)) :=
    Summable.mul_left (8 : ℝ) h₁
  refine Summable.congr h₂ ?_
  intro n
  ring

private lemma pp_partial_eq_range (m : ℕ) :
    (∑ p ∈ m.primesLE, Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2)) =
      ∑ k ∈ Finset.range (m + 1), ppSqCorr k := by
  have hIcc : (Finset.Icc 0 m : Finset ℕ) = Finset.range (m + 1) := by
    ext k
    simp
  rw [Nat.primesLE_eq_filter_Icc_zero, hIcc]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro p hp
  simp [ppSqCorr]

/-- the same correction, viewed on the subtype of primes -/
private def ppSqCorrPrime (p : Nat.Primes) : ℝ :=
  Real.log (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2)

private lemma tsum_ppSqCorr_eq :
    (∑' p : Nat.Primes, ppSqCorrPrime p) = ∑' n : ℕ, ppSqCorr n := by
  have hs : Function.support ppSqCorr ⊆ {n : ℕ | Nat.Prime n} := by
    intro n hn
    by_contra hnp
    have hprime : Nat.Prime n := by
      by_contra h
      simp [ppSqCorr, h] at hn
    exact hnp hprime
  have hiff := (hasSum_subtype_iff_of_support_subset (f := ppSqCorr)
    (a := ∑' n : ℕ, ppSqCorr n) (s := {n : ℕ | Nat.Prime n}) hs)
  have hL : HasSum (fun p : Nat.Primes => ppSqCorr p.1) (∑' n : ℕ, ppSqCorr n) :=
    hiff.2 (Summable.hasSum summable_ppSqCorr)
  have hcong : ∀ p : Nat.Primes, ppSqCorrPrime p = ppSqCorr p.1 := by
    intro p
    simp [ppSqCorrPrime, ppSqCorr, p.2]
  have hbT : HasSum ppSqCorrPrime (∑' n : ℕ, ppSqCorr n) :=
    HasSum.congr_fun hL (fun p => hcong p)
  have hb : (∑' p : Nat.Primes, ppSqCorrPrime p) = ∑' n : ℕ, ppSqCorr n :=
    HasSum.tsum_eq hbT
  exact hb

private lemma pp_tendsto_range_add_one :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range (m + 1), ppSqCorr k) atTop
      (nhds (∑' n : ℕ, ppSqCorr n)) := by
  have h := Summable.tendsto_sum_tsum_nat summable_ppSqCorr
  exact h.comp (Filter.tendsto_add_atTop_nat 1)

/-- correction sums converge (real variable): `Σ_{p ≤ x} log (1 - 1/(p-1)^2)` has a limit. -/
private theorem ppSqCorr_partial_tendsto :
    ∃ κ : ℝ, Filter.Tendsto (fun x : ℝ =>
      ∑ p ∈ (⌊x⌋₊).primesLE, Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2))
      Filter.atTop (nhds κ) := by
  have hNat : Tendsto (fun m : ℕ => ∑ p ∈ m.primesLE, Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2))
      atTop (nhds (∑' n : ℕ, ppSqCorr n)) := by
    refine Filter.Tendsto.congr' ?_ pp_tendsto_range_add_one
    filter_upwards with m
    exact (pp_partial_eq_range m).symm
  have hFloor : Tendsto (fun x : ℝ =>
      ∑ p ∈ (⌊x⌋₊).primesLE, Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2)) atTop
      (nhds (∑' n : ℕ, ppSqCorr n)) :=
    hNat.comp (tendsto_nat_floor_atTop (α := ℝ))
  refine ⟨∑' p : Nat.Primes, ppSqCorrPrime p, ?_⟩
  rwa [tsum_ppSqCorr_eq]

/-! ## The main product and its logarithm -/

/-- the factor `(1 - 1/(p-1))` attached to an odd prime `p` -/
private def ppFactor (p : ℕ) : ℝ := 1 - 1 / ((p : ℝ) - 1)

/-- the set of odd primes `≤ ⌊z⌋₊` -/
private def ppSet (z : ℝ) : Finset ℕ :=
  (Nat.primesLE (⌊z⌋₊)).filter (fun p : ℕ => p ≠ 2)

/-- the product over odd primes `≤ ⌊z⌋₊` of `(1 - 1/(p-1))` -/
private def ppProd (z : ℝ) : ℝ := ∏ p ∈ ppSet z, ppFactor p

/-- `Σ_{odd p ≤ ⌊z⌋₊} log(1 - 1/(p-1))` -/
private def ppMainLogSum (z : ℝ) : ℝ := ∑ p ∈ ppSet z, Real.log (ppFactor p)

/-- `Σ_{odd p ≤ ⌊z⌋₊} log(1 - 1/(p-1)^2)` -/
private def ppCorrSum (z : ℝ) : ℝ := ∑ p ∈ ppSet z, Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- `Σ_{p ≤ ⌊z⌋₊} log(1 - 1/(p-1)^2)` (all primes; the `p = 2` summand is zero) -/
private def ppCorrSumAll (z : ℝ) : ℝ :=
  ∑ p ∈ (⌊z⌋₊).primesLE, Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- `Σ_{p ≤ ⌊z⌋₊} log (p/(p-1))` -/
private def ppRatioSum (z : ℝ) : ℝ :=
  ∑ p ∈ (⌊z⌋₊).primesLE, Real.log ((p : ℝ) / ((p : ℝ) - 1))

/-- `log (log z) + Σ_{odd p ≤ ⌊z⌋₊} log(1 - 1/(p-1))` -/
private def ppLogSum (z : ℝ) : ℝ :=
  Real.log (Real.log z) + ppMainLogSum z

private lemma ppFactor_pos {p : ℕ} (hp : 3 ≤ p) : 0 < ppFactor p := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hx : (2 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hx0 : 0 < (p : ℝ) - 1 := by linarith
  have hinv : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hx
  have hlt : 1 / ((p : ℝ) - 1) < 1 := lt_of_le_of_lt hinv (by norm_num)
  unfold ppFactor
  linarith

private lemma ppFactor_ne_zero {p : ℕ} (hp : 3 ≤ p) : ppFactor p ≠ 0 := by
  exact ne_of_gt (ppFactor_pos hp)

private lemma mem_ppSet {z : ℝ} {p : ℕ} (hp : p ∈ ppSet z) :
    p ∈ Nat.primesLE (⌊z⌋₊) ∧ p ≠ 2 := by
  simpa [ppSet] using hp

private lemma three_le_of_mem_ppSet {z : ℝ} {p : ℕ} (hp : p ∈ ppSet z) : 3 ≤ p := by
  have h := mem_ppSet hp
  have hpp : Nat.Prime p := (Nat.mem_primesLE.mp h.1).2
  have h2 : 2 ≤ p := Nat.Prime.two_le hpp
  omega

/-- `log (1 - 1/(p-1)) = log (1 - 1/(p-1)^2) − log (p/(p-1))` for an odd prime `p`. -/
private lemma pp_log_identity {p : ℕ} (hpp : Nat.Prime p) (hp2 : p ≠ 2) :
    Real.log (ppFactor p) =
      Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2) - Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ p := Nat.Prime.two_le hpp
    omega
  have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hm1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hm1
  have hnum : (1 - 1 / ((p : ℝ) - 1) ^ 2) ≠ 0 := ppSqCorr_arg_ne_zero hp3
  have hden : ((p : ℝ) / ((p : ℝ) - 1)) ≠ 0 := by
    exact div_ne_zero (ne_of_gt hp0) hm1ne
  rw [← Real.log_div hnum hden]
  congr 1
  unfold ppFactor
  field_simp [hm1ne]
  ring

private lemma ppProd_log_eq : ∀ z : ℝ, Real.log (ppProd z) = ppMainLogSum z := by
  intro z
  unfold ppProd ppMainLogSum
  refine Real.log_prod ?_
  intro p hp
  exact ppFactor_ne_zero (three_le_of_mem_ppSet hp)

private lemma ppProd_pos (z : ℝ) : 0 < ppProd z := by
  unfold ppProd
  refine Finset.prod_pos ?_
  intro p hp
  exact ppFactor_pos (three_le_of_mem_ppSet hp)

/-- `primesLE n = {2} ∪ {odd primes ≤ n}` for `2 ≤ n`. -/
private lemma primesLE_insert_two (n : ℕ) (hn : 2 ≤ n) :
    Nat.primesLE n = insert 2 ((Nat.primesLE n).filter (fun p : ℕ => p ≠ 2)) := by
  ext p
  constructor
  · intro hpA
    by_cases hp2 : p = 2
    · simp [hp2]
    · rw [Finset.mem_insert]
      right
      exact Finset.mem_filter.mpr ⟨hpA, hp2⟩
  · intro hp
    rw [Finset.mem_insert] at hp
    rcases hp with rfl | hpB
    · exact Nat.mem_primesLE.mpr ⟨hn, Nat.prime_two⟩
    · exact (Finset.mem_filter.mp hpB).1

private lemma pp_ratioSum_eq (z : ℝ) (hz : 2 ≤ z) :
    ppRatioSum z = Real.log 2 + ∑ p ∈ ppSet z, Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hzfloor : 2 ≤ (⌊z⌋₊ : ℕ) := Nat.le_floor hz
  change (∑ p ∈ (⌊z⌋₊).primesLE, Real.log ((p : ℝ) / ((p : ℝ) - 1))) =
    Real.log 2 + ∑ p ∈ ppSet z, Real.log ((p : ℝ) / ((p : ℝ) - 1))
  rw [primesLE_insert_two (⌊z⌋₊) hzfloor]
  rw [Finset.sum_insert (by simp)]
  have h2 : Real.log (((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1)) = Real.log 2 := by
    have harg : (((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1)) = (2 : ℝ) := by norm_num
    rw [harg]
  rw [h2]
  rfl

private lemma pp_corrSumAll_eq (z : ℝ) (hz : 2 ≤ z) : ppCorrSumAll z = ppCorrSum z := by
  have hzfloor : 2 ≤ (⌊z⌋₊ : ℕ) := Nat.le_floor hz
  change (∑ p ∈ (⌊z⌋₊).primesLE, Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2)) =
    ∑ p ∈ ppSet z, Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2)
  rw [primesLE_insert_two (⌊z⌋₊) hzfloor]
  rw [Finset.sum_insert (by simp)]
  have hzero : Real.log (1 - 1 / (((2 : ℕ) : ℝ) - 1) ^ 2) = 0 := by
    norm_num
  rw [hzero]
  unfold ppSet
  simp

/-- decomposition of the log-sum over odd primes. -/
private lemma ppMainLogSum_eq (z : ℝ) (hz : 2 ≤ z) :
    ppMainLogSum z = ppCorrSum z - (ppRatioSum z - Real.log 2) := by
  have hsumS : (∑ p ∈ ppSet z, Real.log ((p : ℝ) / ((p : ℝ) - 1))) =
      ppRatioSum z - Real.log 2 := by
    have h := pp_ratioSum_eq z hz
    linarith
  have hstep1 : ppMainLogSum z =
      ∑ p ∈ ppSet z,
        (Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2) - Real.log ((p : ℝ) / ((p : ℝ) - 1))) := by
    unfold ppMainLogSum
    refine Finset.sum_congr rfl ?_
    intro p hp
    exact pp_log_identity (Nat.mem_primesLE.mp (mem_ppSet hp).1).2 (mem_ppSet hp).2
  rw [hstep1]
  rw [Finset.sum_sub_distrib]
  unfold ppCorrSum
  rw [← hsumS]

/-- the key identity for the logarithm of the whole expression. -/
private lemma ppLogSum_eq (z : ℝ) (hz : 2 ≤ z) :
    ppLogSum z = ppCorrSum z + Real.log 2 - (ppRatioSum z - Real.log (Real.log z)) := by
  unfold ppLogSum
  rw [ppMainLogSum_eq z hz]
  ring

/-- `log (log z) + Σ log(1 - 1/(p-1))` tends to `κ + log 2 − γ`. -/
private lemma ppLogSum_tendsto :
    ∃ κ : ℝ, Filter.Tendsto ppLogSum Filter.atTop (nhds (κ + Real.log 2 - Real.eulerMascheroniConstant)) := by
  rcases ppSqCorr_partial_tendsto with ⟨κ, hκ⟩
  refine ⟨κ, ?_⟩
  have hM3 := sum_log_prime_ratio_real_tendsto
  have hM3' : Tendsto (fun z : ℝ => ppRatioSum z - Real.log (Real.log z)) atTop
      (nhds Real.eulerMascheroniConstant) := by
    simpa [ppRatioSum] using hM3
  have hAll : Tendsto (fun z : ℝ => ppCorrSumAll z) atTop (nhds κ) := by
    simpa [ppCorrSumAll] using hκ
  have hcorr : Tendsto (fun z : ℝ => ppCorrSum z) atTop (nhds κ) := by
    refine Filter.Tendsto.congr' ?_ hAll
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with z hz
    exact pp_corrSumAll_eq z hz
  have hcorr' : Tendsto (fun z : ℝ => ppCorrSum z + Real.log 2) atTop
      (nhds (κ + Real.log 2)) := by
    simpa using hcorr.add tendsto_const_nhds
  have hdiff : Tendsto (fun z : ℝ =>
      (ppCorrSum z + Real.log 2) - (ppRatioSum z - Real.log (Real.log z))) atTop
      (nhds (κ + Real.log 2 - Real.eulerMascheroniConstant)) := hcorr'.sub hM3'
  refine Filter.Tendsto.congr' ?_ hdiff
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with z hz
  exact (ppLogSum_eq z hz).symm

/-- the actual theorem: `log z * (product over odd primes ≤ z)` tends to a positive limit. -/
theorem primeProduct_oneSubInvPred_log_tendsto_pos :
    ∃ L : ℝ, 0 < L ∧
      Filter.Tendsto (fun z : ℝ =>
        Real.log z *
          (∏ p ∈ (Nat.primesLE (⌊z⌋₊)).filter (fun p : ℕ => p ≠ 2),
            (1 - 1 / ((p : ℝ) - 1))))
        Filter.atTop (nhds L) := by
  rcases ppLogSum_tendsto with ⟨κ, hκ⟩
  let c : ℝ := κ + Real.log 2 - Real.eulerMascheroniConstant
  let L : ℝ := Real.exp c
  refine ⟨L, Real.exp_pos c, ?_⟩
  -- `L`-tendsto for the real function `z ↦ log z * ppProd z`
  have hc : Filter.Tendsto ppLogSum Filter.atTop (nhds c) := by
    simpa [c] using hκ
  have hexp : Tendsto (fun z : ℝ => Real.exp (ppLogSum z)) atTop (nhds L) := by
    have hcont : Tendsto Real.exp (nhds c) (nhds (Real.exp c)) :=
      Real.continuous_exp.tendsto c
    simpa [Function.comp_def, L] using hcont.comp hc
  have hf : Tendsto (fun z : ℝ => Real.log z * ppProd z) atTop (nhds L) := by
    refine Filter.Tendsto.congr' ?_ hexp
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
    have hlogz : 0 < Real.log z := Real.log_pos hz
    have hprod0 : 0 < ppProd z := ppProd_pos z
    have hpos : 0 < Real.log z * ppProd z := mul_pos hlogz hprod0
    have hmain : Real.log (Real.log z * ppProd z) = ppLogSum z := by
      unfold ppLogSum
      rw [Real.log_mul (ne_of_gt hlogz) (ne_of_gt hprod0)]
      rw [ppProd_log_eq z]
    calc
      Real.exp (ppLogSum z) = Real.exp (Real.log (Real.log z * ppProd z)) := by rw [hmain]
      _ = Real.log z * ppProd z := Real.exp_log hpos
  -- convert to the expression in the statement
  simpa [ppProd, ppFactor, ppSet] using hf

end

end Commons.NumberTheory.Mertens
