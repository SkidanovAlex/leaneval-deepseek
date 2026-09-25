import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_div_sub_log_bounded
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_le_three_sqrt
import Submission.Commons.NumberTheory.Chebyshev.lcmUpto_le_three_pow
import Submission.Commons.NumberTheory.Chebyshev.theta_lower_finite_range

/-!
# A lower bound `θ(x) ≥ 9x/10` for `x ≥ 1530`

The proof uses the classical Chebyshev weight function
`W t = ⌊t⌋ - ⌊t/2⌋ - ⌊t/3⌋ - ⌊t/5⌋ + ⌊t/30⌋`,
which takes values in `{0,1}`.  Since
`∑_n Λ n · W (x/n) = log(⌊x⌋!) - log(⌊x/2⌋!) - log(⌊x/3⌋!) - log(⌊x/5⌋!) + log(⌊x/30⌋!)`
(this is a combination of the identity `∑_{d ≤ N} Λ d ⌊N/d⌋ = log (N!)`) and
`W ≤ 1`, we get the lower bound `ψ(x) ≥ (that log combination)`, which by Stirling's
formula is `≥ 0.9212…x - log x - O(1)`.  Combined with `ψ - θ ≤ 3√x` this yields
`θ(x) ≥ 9x/10` for `x` beyond about `2.5·10^4`, and the remaining finite range is
checked by computation.
-/

namespace Commons.NumberTheory.Chebyshev
namespace ThetaLower

open Finset
open scoped BigOperators

noncomputable section

/-- The Chebyshev weight function, in the natural-number form. -/
def Wn (N : ℕ) : ℤ := (N : ℤ) - (N / 2 : ℕ) - (N / 3 : ℕ) - (N / 5 : ℕ) + (N / 30 : ℕ)

/-- `Wn` is 30-periodic. -/
lemma Wn_add_30 (N : ℕ) : Wn (N + 30) = Wn N := by
  unfold Wn
  have h2 : (N + 30) / 2 = N / 2 + 15 := by omega
  have h3 : (N + 30) / 3 = N / 3 + 10 := by omega
  have h5 : (N + 30) / 5 = N / 5 + 6 := by omega
  have h30 : (N + 30) / 30 = N / 30 + 1 := by omega
  rw [h2, h3, h5, h30]
  push_cast
  ring

/-- `Wn (N + 30 * k) = Wn N`. -/
lemma Wn_add_30_mul (N : ℕ) : ∀ k : ℕ, Wn (N + 30 * k) = Wn N := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h : N + 30 * (k + 1) = (N + 30 * k) + 30 := by ring
    rw [h, Wn_add_30, ih]

/-- `Wn N` depends only on `N % 30`. -/
lemma Wn_eq_mod (N : ℕ) : Wn N = Wn (N % 30) := by
  have h : N = N % 30 + 30 * (N / 30) := by rw [Nat.mod_add_div]
  conv_lhs => rw [h]
  exact Wn_add_30_mul (N % 30) (N / 30)

/-- The weight takes values in `{0,1}`. -/
lemma Wn_mem (N : ℕ) : 0 ≤ Wn N ∧ Wn N ≤ 1 := by
  rw [Wn_eq_mod N]
  have : ∀ M ∈ Finset.range 30, (0 : ℤ) ≤ Wn M ∧ Wn M ≤ 1 := by decide
  exact this (N % 30) (Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))

/-- The weight function on the reals. -/
def Wm (t : ℝ) : ℤ := ⌊t⌋₊ - ⌊t / 2⌋₊ - ⌊t / 3⌋₊ - ⌊t / 5⌋₊ + ⌊t / 30⌋₊

lemma Wm_eq_Wn (t : ℝ) : Wm t = Wn ⌊t⌋₊ := by
  have h2 : ⌊t / 2⌋₊ = ⌊t⌋₊ / 2 := Nat.floor_div_natCast t 2
  have h3 : ⌊t / 3⌋₊ = ⌊t⌋₊ / 3 := Nat.floor_div_natCast t 3
  have h5 : ⌊t / 5⌋₊ = ⌊t⌋₊ / 5 := Nat.floor_div_natCast t 5
  have h30 : ⌊t / 30⌋₊ = ⌊t⌋₊ / 30 := Nat.floor_div_natCast t 30
  unfold Wm Wn
  rw [h2, h3, h5, h30]

/-- The weight function on the reals takes values in `{0,1}`. -/
lemma Wm_mem (t : ℝ) : 0 ≤ Wm t ∧ Wm t ≤ 1 := by
  rw [Wm_eq_Wn]
  exact Wn_mem _


/-- The bracket of the weight identity. -/
def br (N n : ℕ) : ℝ :=
  ((N / n : ℕ) : ℝ) - ((N / 2 / n : ℕ) : ℝ) - ((N / 3 / n : ℕ) : ℝ)
    - ((N / 5 / n : ℕ) : ℝ) + ((N / 30 / n : ℕ) : ℝ)

lemma div_div_comm' (N d n : ℕ) : N / d / n = N / n / d := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- Each bracket component equals the corresponding real floor. -/
lemma br_component (N d n : ℕ) : ((N / d / n : ℕ) : ℝ) = (⌊(N : ℝ) / n / d⌋₊ : ℝ) := by
  have h1 : N / d / n = N / (d * n) := Nat.div_div_eq_div_mul N d n
  have h2 : N / (d * n) = N / (n * d) := by rw [Nat.mul_comm]
  have h3 : N / (n * d) = N / n / d := (Nat.div_div_eq_div_mul N n d).symm
  rw [h1, h2, h3, Nat.floor_div_natCast ((N : ℝ) / n) d,
    Nat.floor_div_natCast (N : ℝ) n, Nat.floor_natCast]

lemma br_eq_Wm (N n : ℕ) : br N n = ((Wm ((N : ℝ) / n)) : ℝ) := by
  have h1 : ((N / 1 / n : ℕ) : ℝ) = (⌊(N : ℝ) / n / 1⌋₊ : ℝ) := by
    simpa using br_component N 1 n
  have h2 := br_component N 2 n
  have h3 := br_component N 3 n
  have h5 := br_component N 5 n
  have h30 := br_component N 30 n
  simp only [Nat.div_one] at h1
  unfold br Wm
  rw [h1, h2, h3, h5, h30]
  push_cast
  ring

lemma br_mem (N n : ℕ) : 0 ≤ br N n ∧ br N n ≤ 1 := by
  have h := Wm_mem ((N : ℝ) / n)
  rw [br_eq_Wm]
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- Extension of `∑_{d ≤ N} Λ d · ⌊N/d⌋ = log (N!)` to the full range `Icc 1 N`. -/
lemma sum_vonMangoldt_div_eq_log_factorial (N d : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.vonMangoldt n : ℝ) * ((N / d / n : ℕ) : ℝ)
      = Real.log ((N / d).factorial : ℝ) := by
  rw [← Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_mul_div_eq_log_factorial (N / d)]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 (Nat.div_le_self N d)⟩
  · intro x hxN hxnot
    rw [Finset.mem_Icc] at hxN
    have hx1 : 1 ≤ x := hxN.1
    have hxg : N / d < x := by
      by_contra hle
      exact hxnot (Finset.mem_Icc.mpr ⟨hx1, not_lt.mp hle⟩)
    rw [Nat.div_eq_of_lt hxg, Nat.cast_zero, mul_zero]

/-- The `d = 1` case of the extension lemma, in the form used below. -/
lemma sum_vonMangoldt_div_one_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * ((N / n : ℕ) : ℝ)
      = Real.log ((N.factorial : ℕ) : ℝ) := by
  simpa using sum_vonMangoldt_div_eq_log_factorial N 1

/-- The log-factorial combination identity. -/
lemma weight_sum_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * br N n
      = Real.log ((N.factorial : ℕ) : ℝ)
        - Real.log (((N / 2).factorial : ℕ) : ℝ)
        - Real.log (((N / 3).factorial : ℕ) : ℝ)
        - Real.log (((N / 5).factorial : ℕ) : ℝ)
        + Real.log (((N / 30).factorial : ℕ) : ℝ) := by
  have hsplit : ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * br N n
      = (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * ((N / n : ℕ) : ℝ))
        - (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * ((N / 2 / n : ℕ) : ℝ))
        - (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * ((N / 3 / n : ℕ) : ℝ))
        - (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * ((N / 5 / n : ℕ) : ℝ))
        + (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * ((N / 30 / n : ℕ) : ℝ)) := by
    simp only [br, mul_sub, mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
  rw [hsplit, sum_vonMangoldt_div_one_eq N,
      sum_vonMangoldt_div_eq_log_factorial N 2,
      sum_vonMangoldt_div_eq_log_factorial N 3,
      sum_vonMangoldt_div_eq_log_factorial N 5,
      sum_vonMangoldt_div_eq_log_factorial N 30]

/-- **Chebyshev's weight-function lower bound for `ψ`.** -/
theorem psi_ge_weight (N : ℕ) :
    Real.log (((N / 30).factorial : ℕ) : ℝ) + Real.log ((N.factorial : ℕ) : ℝ)
      - Real.log (((N / 2).factorial : ℕ) : ℝ)
      - Real.log (((N / 3).factorial : ℕ) : ℝ)
      - Real.log (((N / 5).factorial : ℕ) : ℝ) ≤ Chebyshev.psi (N : ℝ) := by
  have hpsi : Chebyshev.psi (N : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Finset.Icc_eq_cons_Ioc (Nat.zero_le N),
      Finset.sum_cons]
    rw [show Finset.Ioc 0 N = Finset.Icc 1 N from by
      ext n; simp [Finset.mem_Ioc, Finset.mem_Icc]; omega]
    simp
  rw [hpsi]
  have h := weight_sum_eq N
  have h2 : Real.log (((N / 30).factorial : ℕ) : ℝ) + Real.log ((N.factorial : ℕ) : ℝ)
      - Real.log (((N / 2).factorial : ℕ) : ℝ)
      - Real.log (((N / 3).factorial : ℕ) : ℝ)
      - Real.log (((N / 5).factorial : ℕ) : ℝ)
      = Real.log ((N.factorial : ℕ) : ℝ)
        - Real.log (((N / 2).factorial : ℕ) : ℝ)
        - Real.log (((N / 3).factorial : ℕ) : ℝ)
        - Real.log (((N / 5).factorial : ℕ) : ℝ)
        + Real.log (((N / 30).factorial : ℕ) : ℝ) := by ring
  rw [h2, ← h]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨h1, h2'⟩ := br_mem N n
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by positivity
  nlinarith [h1, h2', hΛ]


/-- Stirling comparison: replace each `log (k!)` by its Stirling bound. -/
lemma stirling_combo_le (N : ℕ) (hN : 1 ≤ N) :
    hLog (N : ℝ) - ALog (N / 2) - ALog (N / 3) - ALog (N / 5) + hLog ((N / 30 : ℕ) : ℝ)
      ≤ Real.log ((N.factorial : ℕ) : ℝ)
        - Real.log (((N / 2).factorial : ℕ) : ℝ)
        - Real.log (((N / 3).factorial : ℕ) : ℝ)
        - Real.log (((N / 5).factorial : ℕ) : ℝ)
        + Real.log (((N / 30).factorial : ℕ) : ℝ) := by
  have h1 : hLog (N : ℝ) ≤ Real.log ((N.factorial : ℕ) : ℝ) := log_factorial_ge_hLog N hN
  have h30 : hLog ((N / 30 : ℕ) : ℝ) ≤ Real.log (((N / 30).factorial : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N / 30) with h | h
    · rw [h]
      simp [hLog, Nat.factorial_zero]
    · exact log_factorial_ge_hLog (N / 30) h
  have hn2 : -ALog (N / 2) ≤ -Real.log (((N / 2).factorial : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N / 2) with h | h
    · rw [h]; simp [ALog, Nat.factorial_zero]
    · have := log_factorial_le_ALog (N / 2) h; linarith
  have hn3 : -ALog (N / 3) ≤ -Real.log (((N / 3).factorial : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N / 3) with h | h
    · rw [h]; simp [ALog, Nat.factorial_zero]
    · have := log_factorial_le_ALog (N / 3) h; linarith
  have hn5 : -ALog (N / 5) ≤ -Real.log (((N / 5).factorial : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N / 5) with h | h
    · rw [h]; simp [ALog, Nat.factorial_zero]
    · have := log_factorial_le_ALog (N / 5) h; linarith
  linarith




/-- The real-argument version of `ALog`. -/
def ALogR (y : ℝ) : ℝ := y * Real.log y - y + 1 + Real.log y / 2

lemma ALog_eq_ALogR (n : ℕ) : ALog n = ALogR (n : ℝ) := rfl

/-- Basic floor facts: `N/d - 1 < (N/d : ℕ) ≤ N/d`. -/
lemma div_floor_facts {N d : ℕ} (hd : 1 ≤ d) :
    ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d ∧ (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h1 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have hmul : N < (N / d + 1) * d :=
    (Nat.div_lt_iff_lt_mul (show 0 < d by omega)).mp (Nat.lt_succ_self _)
  have h2 : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
    have h : (N : ℝ) < ((N / d + 1) * d : ℕ) := by exact_mod_cast hmul
    push_cast at h
    rw [div_lt_iff₀ hd0]; linarith
  exact ⟨h1, h2⟩

/-- Upper bound for `ALog (N/d)` in terms of the real argument `N/d`, for `d ≤ N`. -/
lemma ALog_div_le {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    ALog (N / d) ≤ ((N : ℝ) / d) * Real.log ((N : ℝ) / d) - (N : ℝ) / d + Real.log N / 2 + 2 := by
  obtain ⟨h1, h2⟩ := div_floor_facts (N := N) hd
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans hd hdN)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hnz : 1 ≤ N / d := Nat.one_le_div_iff (by omega) |>.mpr hdN
  have hn1 : (1 : ℝ) ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast hnz
  have hlog0 : 0 ≤ Real.log ((N / d : ℕ) : ℝ) := Real.log_nonneg hn1
  have hpos : 0 < (N : ℝ) / d := lt_of_lt_of_le zero_lt_one (le_trans hn1 h1)
  have hy1 : (1 : ℝ) ≤ (N : ℝ) / d := le_trans hn1 h1
  have hlog1 : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log ((N : ℝ) / d) :=
    Real.log_le_log (by linarith) h1
  have hlogy : Real.log ((N : ℝ) / d) ≤ Real.log N := by
    rw [Real.log_le_log_iff (by positivity) (by linarith)]
    exact div_le_self (by linarith) (by exact_mod_cast (by omega : (1:ℕ) ≤ d))
  have hlogN' : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N := le_trans hlog1 hlogy
  have hmono : ((N / d : ℕ) : ℝ) * Real.log ((N / d : ℕ) : ℝ)
      ≤ ((N : ℝ) / d) * Real.log ((N : ℝ) / d) :=
    mul_le_mul h1 hlog1 hlog0 (le_of_lt hpos)
  unfold ALog
  have hloghalf : Real.log ((N / d : ℕ) : ℝ) / 2 ≤ Real.log N / 2 := by linarith
  linarith [hmono, h2, hloghalf]

/-- `log (5/4) ≥ 2231/10000`. -/
lemma log_five_quarters_ge : (2231 / 10000 : ℝ) ≤ Real.log (5 / 4) := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 5 / 4)]
  have h := Real.exp_bound' (x := (2231 / 10000 : ℝ)) (by norm_num) (by norm_num)
    (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial] at h
  norm_num at h ⊢
  linarith

/-- `log 5 ≥ 160938/100000`. -/
lemma log5_ge_num : (160938 / 100000 : ℝ) ≤ Real.log 5 := by
  have h : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4) := by
    rw [show (5 : ℝ) = 4 * (5 / 4) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h]
  have h2 : (69314 / 100000 : ℝ) ≤ Real.log 2 := log2_ge_num
  have h54 : (2231 / 10000 : ℝ) ≤ Real.log (5 / 4) := log_five_quarters_ge
  linarith

/-- Numeric: `λ ≥ 0.92` where `λ = (7/15) log 2 + (3/10) log 3 + (1/6) log 5`. -/
lemma lambda_ge :
    (23 / 25 : ℝ) ≤ (7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5 := by
  have h2 : (69314 / 100000 : ℝ) ≤ Real.log 2 := log2_ge_num
  have h3 : (109860 / 100000 : ℝ) ≤ Real.log 3 := log3_ge_num
  have h5 : (160938 / 100000 : ℝ) ≤ Real.log 5 := log5_ge_num
  linarith

/-- `hLog N ≥ N log N - N` for `N ≥ 1`. -/
lemma hLog_ge (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) ≤ hLog (N : ℝ) := by
  have hp : 0 ≤ Real.log (2 * Real.pi * (N : ℝ)) := by
    apply Real.log_nonneg
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [Real.pi_gt_three, hN1]
  unfold hLog
  linarith

/-- Lower bound for `hLog` at `⌊N/30⌋`. -/
lemma hLog_div_ge {N : ℕ} (hN : 30 ≤ N) :
    ((N : ℝ) / 30) * Real.log ((N : ℝ) / 30) - (N : ℝ) / 30 - Real.log (N : ℝ) - 1
      ≤ hLog ((N / 30 : ℕ) : ℝ) := by
  obtain ⟨h1, h2⟩ := div_floor_facts (N := N) (d := 30) (by norm_num)
  have hypos : (0 : ℝ) < (N : ℝ) / 30 := by positivity
  have hnpos : (0 : ℝ) < ((N / 30 : ℕ) : ℝ) := by
    have : 0 < N / 30 := by omega
    exact_mod_cast this
  have hy1 : (1 : ℝ) ≤ (N : ℝ) / 30 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 30)]
    exact_mod_cast (by omega : 1 * 30 ≤ N)
  have hlogn : Real.log ((N / 30 : ℕ) : ℝ) ≤ Real.log ((N : ℝ) / 30) :=
    Real.log_le_log hnpos h1
  -- key: `n * log n ≥ y * log y - log y - 1`
  have hkey : ((N : ℝ) / 30) * Real.log ((N : ℝ) / 30) - Real.log ((N : ℝ) / 30) - 1
      ≤ ((N / 30 : ℕ) : ℝ) * Real.log ((N / 30 : ℕ) : ℝ) := by
    have hratio : Real.log ((N : ℝ) / 30) - Real.log ((N / 30 : ℕ) : ℝ)
        ≤ ((N : ℝ) / 30 - ((N / 30 : ℕ) : ℝ)) / ((N / 30 : ℕ) : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (div_pos hypos hnpos)
      rw [Real.log_div (ne_of_gt hypos) (ne_of_gt hnpos)] at h
      have he : (N : ℝ) / 30 / ((N / 30 : ℕ) : ℝ) - 1
          = ((N : ℝ) / 30 - ((N / 30 : ℕ) : ℝ)) / ((N / 30 : ℕ) : ℝ) := by
        rw [sub_div, div_self (ne_of_gt hnpos)]
      linarith [h, he]
    have hmul : ((N / 30 : ℕ) : ℝ)
          * (Real.log ((N : ℝ) / 30) - Real.log ((N / 30 : ℕ) : ℝ))
        ≤ (N : ℝ) / 30 - ((N / 30 : ℕ) : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hratio (le_of_lt hnpos)
      have hc : ((N / 30 : ℕ) : ℝ)
          * (((N : ℝ) / 30 - ((N / 30 : ℕ) : ℝ)) / ((N / 30 : ℕ) : ℝ))
          = (N : ℝ) / 30 - ((N / 30 : ℕ) : ℝ) := by
        rw [mul_div_cancel₀ _ (ne_of_gt hnpos)]
      linarith [h, hc]
    have hfac : 0 ≤ (((N / 30 : ℕ) : ℝ) - (N : ℝ) / 30 + 1)
        * (Real.log ((N : ℝ) / 30) + 1) := by
      apply mul_nonneg
      · linarith
      · have : 0 ≤ Real.log ((N : ℝ) / 30) := Real.log_nonneg hy1
        linarith
    have hid : ((N / 30 : ℕ) : ℝ) * Real.log ((N : ℝ) / 30)
          - ((N : ℝ) / 30 - ((N / 30 : ℕ) : ℝ))
          - (((N : ℝ) / 30) * Real.log ((N : ℝ) / 30) - Real.log ((N : ℝ) / 30) - 1)
        = (((N / 30 : ℕ) : ℝ) - (N : ℝ) / 30 + 1)
          * (Real.log ((N : ℝ) / 30) + 1) := by ring
    have hstep : ((N : ℝ) / 30) * Real.log ((N : ℝ) / 30) - Real.log ((N : ℝ) / 30) - 1
        ≤ ((N / 30 : ℕ) : ℝ) * Real.log ((N : ℝ) / 30)
          - ((N : ℝ) / 30 - ((N / 30 : ℕ) : ℝ)) := by
      linarith [hfac, hid]
    have hnm : ((N / 30 : ℕ) : ℝ) * Real.log ((N : ℝ) / 30)
          - ((N : ℝ) / 30 - ((N / 30 : ℕ) : ℝ))
        ≤ ((N / 30 : ℕ) : ℝ) * Real.log ((N / 30 : ℕ) : ℝ) := by
      linarith [hmul]
    linarith [hstep, hnm]
  have hlogyN : Real.log ((N : ℝ) / 30) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log hypos
    exact div_le_self (by positivity) (by norm_num)
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi * ((N / 30 : ℕ) : ℝ)) / 2 := by
    apply div_nonneg _ (by norm_num)
    apply Real.log_nonneg
    have hn1 : (1 : ℝ) ≤ ((N / 30 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ N / 30)
    nlinarith [Real.pi_gt_three, hn1]
  rw [show hLog ((N / 30 : ℕ) : ℝ)
      = ((N / 30 : ℕ) : ℝ) * Real.log ((N / 30 : ℕ) : ℝ) - ((N / 30 : ℕ) : ℝ)
        + Real.log (2 * Real.pi * ((N / 30 : ℕ) : ℝ)) / 2 from rfl]
  linarith [hkey, h1, hlogyN, hlog2pi]

/-- **Main Stirling estimate.**  For `N ≥ 30`,
`hLog N - ALog(N/2) - ALog(N/3) - ALog(N/5) + hLog(⌊N/30⌋)
 ≥ λ N - 7 - (5/2) log N` with `λ = (7/15) log 2 + (3/10) log 3 + (1/6) log 5`. -/
lemma weight_stirling_lower (N : ℕ) (hN : 30 ≤ N) :
    Real.log 2 * (7 / 15) * (N : ℝ) + Real.log 3 * (3 / 10) * (N : ℝ)
        + Real.log 5 * (1 / 6) * (N : ℝ) - 7 - (5 / 2) * Real.log (N : ℝ)
      ≤ hLog (N : ℝ) - ALog (N / 2) - ALog (N / 3) - ALog (N / 5)
        + hLog ((N / 30 : ℕ) : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have h2N : 2 ≤ N := by omega
  have h3N : 3 ≤ N := by omega
  have h5N : 5 ≤ N := by omega
  have hLN : (N : ℝ) ≠ 0 := by positivity
  have hA2 := ALog_div_le (N := N) (d := 2) (by norm_num) h2N
  have hA3 := ALog_div_le (N := N) (d := 3) (by norm_num) h3N
  have hA5 := ALog_div_le (N := N) (d := 5) (by norm_num) h5N
  simp only [Nat.cast_ofNat] at hA2 hA3 hA5
  have e2 : Real.log ((N : ℝ) / 2) = Real.log (N : ℝ) - Real.log 2 :=
    Real.log_div hLN (by norm_num)
  have e3 : Real.log ((N : ℝ) / 3) = Real.log (N : ℝ) - Real.log 3 :=
    Real.log_div hLN (by norm_num)
  have e5 : Real.log ((N : ℝ) / 5) = Real.log (N : ℝ) - Real.log 5 :=
    Real.log_div hLN (by norm_num)
  have e30 : Real.log ((N : ℝ) / 30) = Real.log (N : ℝ) - Real.log 30 :=
    Real.log_div hLN (by norm_num)
  have e30' : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  rw [e2] at hA2
  rw [e3] at hA3
  rw [e5] at hA5
  have hH : (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) ≤ hLog (N : ℝ) := hLog_ge N hN1
  have hH30 := hLog_div_ge hN
  rw [e30, e30'] at hH30
  have hkey := hH30
  have hEq : ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ))
        - ((N : ℝ) / 2 * (Real.log (N : ℝ) - Real.log 2) - (N : ℝ) / 2
            + Real.log (N : ℝ) / 2 + 2)
        - ((N : ℝ) / 3 * (Real.log (N : ℝ) - Real.log 3) - (N : ℝ) / 3
            + Real.log (N : ℝ) / 2 + 2)
        - ((N : ℝ) / 5 * (Real.log (N : ℝ) - Real.log 5) - (N : ℝ) / 5
            + Real.log (N : ℝ) / 2 + 2)
        + ((N : ℝ) / 30 * (Real.log (N : ℝ) - (Real.log 2 + Real.log 3 + Real.log 5))
            - (N : ℝ) / 30 - Real.log (N : ℝ) - 1)
      = Real.log 2 * (7 / 15) * (N : ℝ) + Real.log 3 * (3 / 10) * (N : ℝ)
        + Real.log 5 * (1 / 6) * (N : ℝ) - 7 - (5 / 2) * Real.log (N : ℝ) := by
    ring
  linarith [hA2, hA3, hA5, hH, hkey, hEq]

/-- `log N ≤ √N/50 + 2 log 100 - 2` for `N ≥ 1`. -/
lemma log_natCast_le (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) ≤ √(N : ℝ) / 50 + 2 * Real.log 100 - 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hsq : (√(N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsN : Real.log (N : ℝ) = 2 * Real.log (√(N : ℝ)) := by
    have h := Real.log_pow (√(N : ℝ)) 2
    rw [hsq] at h
    rw [h]
    norm_num
  rw [hsN]
  have hspos : (0 : ℝ) < √(N : ℝ) := Real.sqrt_pos.mpr hNpos
  have h1 : Real.log (√(N : ℝ) / 100) ≤ √(N : ℝ) / 100 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlog : Real.log (√(N : ℝ)) = Real.log 100 + Real.log (√(N : ℝ) / 100) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    ring
  linarith [h1, hlog]

/-- `log 100 ≤ 46052/10000`. -/
lemma log100_le : Real.log 100 ≤ (46052 / 10000 : ℝ) := by
  have h : Real.log 100 = 2 * Real.log 2 + 2 * Real.log 5 := by
    rw [show (100 : ℝ) = 2 ^ 2 * 5 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    norm_num
  rw [h]
  have h2 : Real.log 2 ≤ 69316 / 100000 := log2_le_num
  have h5 : Real.log 5 ≤ 160944 / 100000 := log5_le_num
  linarith

/-- `√N ≤ N/173` for `N ≥ 29929`. -/
lemma sqrt_le_div_173 {N : ℕ} (hN : 29929 ≤ N) : √(N : ℝ) ≤ (N : ℝ) / 173 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h : (173 : ℝ) ^ 2 ≤ (N : ℝ) := by
    have h1 : ((29929 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : ((173 : ℝ)) ^ 2 = ((29929 : ℕ) : ℝ) := by norm_num
    linarith
  have h2 : (N : ℝ) ≤ ((N : ℝ) / 173) ^ 2 := by
    rw [div_pow]
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < (173:ℝ)^2)]
    nlinarith [h, hNpos]
  exact h2


/-- For `N ≥ 30000`, `θ(N) ≥ (9/10)(N+1)`. -/
lemma theta_ge_nine_tenths_large (N : ℕ) (hN : 30000 ≤ N) :
    (9 / 10 : ℝ) * ((N : ℝ) + 1) ≤ Chebyshev.theta (N : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have hN30 : 30 ≤ N := by omega
  have hpsi := psi_ge_weight N
  have hstir := stirling_combo_le N hN1
  have hwl := weight_stirling_lower N hN30
  have hlam : (23 / 25 : ℝ) * (N : ℝ)
      ≤ Real.log 2 * (7 / 15) * (N : ℝ) + Real.log 3 * (3 / 10) * (N : ℝ)
        + Real.log 5 * (1 / 6) * (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_right lambda_ge (by positivity : (0 : ℝ) ≤ (N : ℝ))
    linarith [h]
  have hpt := psi_sub_theta_le_three_sqrt (N : ℝ) (by exact_mod_cast hN1)
  have hfin : (79 / 10 : ℝ) + (5 / 2) * Real.log (N : ℝ) + 3 * √(N : ℝ) ≤ (1 / 50 : ℝ) * N := by
    have hlogN := log_natCast_le N hN1
    have h100 := log100_le
    have hsqrt := sqrt_le_div_173 (N := N) (by omega : 29929 ≤ N)
    have hN' : (30000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hb1 : (5 / 2) * Real.log (N : ℝ)
        ≤ √(N : ℝ) / 20 + 5 * (46052 / 10000 : ℝ) - 5 := by
      linarith [hlogN, h100]
    have hb2 : √(N : ℝ) / 20 + 3 * √(N : ℝ) ≤ (61 / 20 : ℝ) * ((N : ℝ) / 173) := by
      linarith [hsqrt]
    linarith [hb1, hb2, hN']
  linarith [hpsi, hstir, hwl, hlam, hpt, hfin]

end

end ThetaLower

end Commons.NumberTheory.Chebyshev

namespace Commons.NumberTheory.Chebyshev

/-- **Chebyshev's lower bound `θ(x) ≥ 9x/10` for `x ≥ 1530`.** -/
theorem theta_lower_ninetenths : ∀ x : ℝ, 1530 ≤ x → (9 / 10) * x ≤ Chebyshev.theta x := by
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  set N : ℕ := ⌊x⌋₊ with hN
  have hN1530 : 1530 ≤ N := Nat.le_floor (by push_cast; exact hx)
  have hxN : x < (N : ℝ) + 1 := by
    rw [hN]; exact Nat.lt_floor_add_one x
  have hth : Chebyshev.theta x = Chebyshev.theta (N : ℝ) := by
    have h := Chebyshev.theta_eq_theta_coe_floor x
    rw [← hN] at h
    exact h
  have hkey : (9 / 10 : ℝ) * ((N : ℝ) + 1) ≤ Chebyshev.theta (N : ℝ) := by
    by_cases h : N ≤ 30000
    · exact Commons.NumberTheory.Chebyshev.theta_lower_finite_range N hN1530 h
    · exact ThetaLower.theta_ge_nine_tenths_large N (by omega)
  rw [hth]
  linarith [hkey, hxN]
