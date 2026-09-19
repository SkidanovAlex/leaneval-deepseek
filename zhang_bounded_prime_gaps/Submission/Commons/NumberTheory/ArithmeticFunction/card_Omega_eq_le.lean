import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.MeasureTheory.Measure.volume_sum_eq_zero_ge_one

/-!
# Almost-prime count bound (upper-bound Selberg--Sathe, fixed k)

The number of `m ≤ N` with exactly `k` prime factors counted with multiplicity
(`Ω m = k`, `ArithmeticFunction.cardFactors`) is at most
`C(k)·N·(log log N)^(k-1)/log N`.

We prove a real-variable version: for `X ≥ 3` and `1 ≤ k` there is a constant
`C` with `#{m ≤ X : Ω m = k} ≤ C·X·(log log X)^(k-1)/log X`.
The result is derived by induction on `k`, starting from the Chebyshev bound
`π(X) ≤ (2·log 4 + 1)·X/log X` and using the decomposition
`#{Ω m = k+1, m ≤ X} ≤ Σ_{p prime, p ≤ √X} #{Ω m = k, m ≤ X/p}`
(valid since every `(k+1)`-almost-prime has a prime factor at most `√X`,
taking the smallest prime factor).  The prime-reciprocal sum over `p ≤ √X`
is bounded by `O(log log X)` via a dyadic argument from the Chebyshev bound.
-/

open scoped ArithmeticFunction.Omega BigOperators
open Finset Real

namespace Commons.NumberTheory.ArithmeticFunction

noncomputable section

section LogPi

/-! ## Logarithm and prime-counting bounds -/

/-- `log x ≤ √x` for `x ≥ 1`. -/
lemma log_le_sqrt_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.sqrt x := by
  by_cases hx4 : x ≤ 4
  · have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith : 0 < x)
    have h1 : Real.log x ≤ 2 * (Real.sqrt x - 1) := by
      have hlog : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hsq
      calc
        Real.log x = Real.log ((Real.sqrt x) ^ 2) := by
          rw [Real.sq_sqrt (le_trans zero_le_one hx)]
        _ = 2 * Real.log (Real.sqrt x) := by
          rw [Real.log_pow]
          norm_num
        _ ≤ 2 * (Real.sqrt x - 1) := by
          gcongr
    have h2 : 2 * (Real.sqrt x - 1) ≤ Real.sqrt x := by
      have hsq2 : Real.sqrt x ≤ 2 := by
        rw [Real.sqrt_le_iff]
        constructor
        · norm_num
        · linarith
      linarith
    exact h1.trans h2
  · have hx4 : 4 < x := lt_of_not_ge hx4
    have hy2 : 2 ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by norm_num) (by linarith : 0 ≤ x)]
      norm_num
      exact hx4.le
    have hly : Real.log (Real.sqrt x) ≤ Real.sqrt x / 2 := by
      -- log y ≤ y / 2 for y ≥ 2
      by_cases hyle : Real.sqrt x ≤ Real.exp 1
      · have h1 : Real.log (Real.sqrt x) ≤ 1 := by
          calc
            Real.log (Real.sqrt x) ≤ Real.log (Real.exp 1) :=
              Real.log_le_log (by linarith : 0 < Real.sqrt x) hyle
            _ = 1 := Real.log_exp 1
        exact le_trans h1 (by linarith : (1 : ℝ) ≤ Real.sqrt x / 2)
      · have he : Real.exp 1 < Real.sqrt x := lt_of_not_ge hyle
        have hy0 : 0 < Real.sqrt x := lt_trans (Real.exp_pos 1) he
        have ha : AntitoneOn (fun y : ℝ => Real.log y / y) (Set.Ici (Real.exp 1)) :=
          Real.log_div_self_antitoneOn
        have hq : Real.log (Real.sqrt x) / Real.sqrt x ≤ 1 / Real.exp 1 := by
          have hyi : Real.sqrt x ∈ Set.Ici (Real.exp 1) := Set.mem_Ici.mpr he.le
          have hei : Real.exp 1 ∈ Set.Ici (Real.exp 1) := Set.mem_Ici.mpr le_rfl
          simpa using (ha hei hyi he.le)
        have h1e2 : (1 : ℝ) / Real.exp 1 ≤ 1 / 2 := by
          have hE : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
          gcongr
        calc
          Real.log (Real.sqrt x) ≤ (1 / Real.exp 1) * Real.sqrt x :=
            (div_le_iff₀ hy0).mp hq
          _ ≤ (1 / 2) * Real.sqrt x := mul_le_mul_of_nonneg_right h1e2 hy0.le
          _ = Real.sqrt x / 2 := by ring
    calc
      Real.log x = Real.log ((Real.sqrt x) ^ 2) := by
        rw [Real.sq_sqrt (by linarith : 0 ≤ x)]
      _ = 2 * Real.log (Real.sqrt x) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ 2 * (Real.sqrt x / 2) := by gcongr
      _ = Real.sqrt x := by ring

/-- `√x ≤ x / log x` for `x ≥ 2`. -/
lemma sqrt_le_id_div_log {x : ℝ} (hx : 2 ≤ x) : Real.sqrt x ≤ x / Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith : 1 < x)
  have h := log_le_sqrt_of_one_le (by linarith : 1 ≤ x)
  rw [le_div_iff₀ hlogpos]
  calc
    Real.sqrt x * Real.log x ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg x)
    _ = x := by simpa [pow_two] using Real.sq_sqrt hx0

/-- Chebyshev-based explicit upper bound for the prime counting function:
`π(x) ≤ (2·log 4 + 1)·x / log x` for `x ≥ 2`. -/
lemma pi_upper_log_real (x : ℝ) (hx : 2 ≤ x) :
    ((⌊x⌋₊.primesLE).card : ℝ) ≤ (2 * Real.log 4 + 1) * x / Real.log x := by
  have hpi := Chebyshev.pi_le_log4_mul_div (by linarith : 1 < x)
  have hsq : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt (by linarith : 0 ≤ x)
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith : 1 < x)
  have hs : Real.sqrt x ≤ x / Real.log x := sqrt_le_id_div_log hx
  have hpi' : ((⌊x⌋₊.primeCounting : ℕ) : ℝ) ≤
      (2 * Real.log 4) * x / Real.log x + Real.sqrt x := by
    calc
      ((⌊x⌋₊.primeCounting : ℕ) : ℝ) ≤ Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x := by
        simpa using hpi
      _ = (2 * Real.log 4) * x / Real.log x + Real.sqrt x := by
        rw [hsq]
        field_simp [hlogpos.ne']
  have hcard : ((⌊x⌋₊.primesLE).card : ℝ) = ((⌊x⌋₊.primeCounting : ℕ) : ℝ) := by
    norm_num [Nat.primesLE_card_eq_primeCounting]
  calc
    ((⌊x⌋₊.primesLE).card : ℝ) = ((⌊x⌋₊.primeCounting : ℕ) : ℝ) := hcard
    _ ≤ (2 * Real.log 4) * x / Real.log x + Real.sqrt x := hpi'
    _ ≤ (2 * Real.log 4) * x / Real.log x + x / Real.log x := by
      gcongr
    _ = (2 * Real.log 4 + 1) * x / Real.log x := by ring


/-- natural-argument prime bound: `#primes ≤ n ≤ (2·log 4+1)·n/log n` for `n ≥ 2`. -/
lemma pi_upper_log_nat (n : ℕ) (hn : 2 ≤ n) :
    ((n.primesLE).card : ℝ) ≤ (2 * Real.log 4 + 1) * (n : ℝ) / Real.log (n : ℝ) := by
  have hx : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have h := pi_upper_log_real (n : ℝ) hx
  have hfl : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
  simpa [hfl] using h
/-- `log 4 ≤ 3/2`. -/
lemma log_four_le_three_halves : Real.log 4 ≤ 3 / 2 := by
  have h := Real.log_two_lt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
  linarith

/-- positivity of the base constant. -/
lemma pi_const_pos : 0 < 2 * Real.log 4 + 1 := by
  have h : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  nlinarith

end LogPi
section Numerics

/-! ## Small explicit constants (log / exp bounds) -/

/-- `2/3 ≤ log 2`. -/
lemma log_two_ge_two_thirds : (2 : ℝ) / 3 ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h
  nlinarith


/-- `log 2 > 0`. -/
lemma log_two_pos : 0 < Real.log 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 3) log_two_ge_two_thirds
/-- `log 2 ≤ 3/4`. -/
lemma log_two_le_three_quarters : Real.log 2 ≤ (3 : ℝ) / 4 := by
  have h := Real.log_two_lt_d9
  nlinarith

/-- `5/2 ≤ exp 1`. -/
lemma exp_one_ge_five_halves : (5 : ℝ) / 2 ≤ Real.exp 1 := by
  have h := Real.exp_one_gt_d9
  nlinarith

/-- `exp 1 ≤ 3`. -/
lemma exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h := Real.exp_one_lt_d9
  nlinarith

/-- `exp(1/10) ≤ 6/5`. -/
lemma exp_tenth_le : Real.exp (1 / 10) ≤ (6 : ℝ) / 5 := by
  have h := Real.exp_bound (x := (1 / 10 : ℝ)) (by norm_num : |(1 / 10 : ℝ)| ≤ 1)
    (n := 1) (by norm_num : 0 < 1)
  norm_num at h
  have habs : |Real.exp (1 / 10) - 1| ≤ 1 / 5 := by simpa using h
  have hle : Real.exp (1 / 10) ≤ 1 + 1 / 5 := by
    linarith [(abs_sub_le_iff.mp habs).1]
  linarith


/-- `(log 2)⁻¹ ≤ 2`. -/
lemma log_two_inv_le_two : (Real.log 2)⁻¹ ≤ 2 := by
  have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [log_two_ge_two_thirds]
  have h0 := one_div_le_one_div_of_le (by norm_num : 0 < (1 / 2 : ℝ)) h2
  norm_num at h0
  exact h0
/-- `log 4 ≥ 4/3`. -/
lemma log_four_ge_four_thirds : (4 : ℝ) / 3 ≤ Real.log 4 := by
  have h2 : (2 : ℝ) / 3 ≤ Real.log 2 := log_two_ge_two_thirds
  rw [Real.log_four_eq]
  nlinarith

/-- `log log 4 ≥ 1/10`. -/
lemma log_log_four_ge : (1 : ℝ) / 10 ≤ Real.log (Real.log 4) := by
  have h4 : (4 : ℝ) / 3 ≤ Real.log 4 := log_four_ge_four_thirds
  have he : Real.exp (1 / 10) ≤ (6 : ℝ) / 5 := exp_tenth_le
  have h : Real.exp (1 / 10) ≤ Real.log 4 := by linarith
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hpos : 0 < Real.exp (1 / 10) := Real.exp_pos _
  have hle := Real.log_le_log hpos h
  rwa [Real.log_exp] at hle

/-- `log 16 ≤ 4`. -/
lemma log_sixteen_le_four : Real.log 16 ≤ 4 := by
  have h2 : Real.log 2 ≤ (3 : ℝ) / 4 := log_two_le_three_quarters
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
    norm_num
  calc
    Real.log 16 = 4 * Real.log 2 := h16
    _ ≤ 3 := by nlinarith
    _ ≤ 4 := by norm_num

/-- `(2·log 4 + 1) ≤ 4`. -/
lemma pi_const_le_four : 2 * Real.log 4 + 1 ≤ 4 := by
  have h2 : Real.log 2 ≤ (3 : ℝ) / 4 := log_two_le_three_quarters
  have h4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
  nlinarith

end Numerics

section Harmonic

/-! ## The prime-reciprocal sum bound (dyadic, from the Chebyshev bound)

`Σ_{p ≤ n} 1/p ≤ 100·(1 + log log n)` for `n ≥ 4`.
-/

def primeRecips (Y : ℝ) : ℝ := ∑ p ∈ ⌊Y⌋₊.primesLE, (1 / (p : ℝ))

lemma primeRecips_nat (n : ℕ) : primeRecips (n : ℝ) = ∑ p ∈ n.primesLE, (1 / (p : ℝ)) := by
  unfold primeRecips
  congr 1
  ext p
  simp only [Nat.mem_primesLE, Nat.floor_natCast]

/-- `Σ_{i ≤ m} 1/i ≤ 1 + log m` (as reals). -/
lemma sum_inv_Icc_one_le_one_add_log (m : ℕ) :
    (∑ i ∈ Icc 1 m, (1 / (i : ℝ))) ≤ 1 + Real.log (m : ℝ) := by
  have h := harmonic_le_one_add_log m
  have heq : (harmonic m : ℝ) = ∑ i ∈ Icc 1 m, (1 / (i : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    simp
  rwa [heq] at h

/-- `Σ_{j=1}^J 1/(j+1) ≤ 1 + log (J+1)`. -/
lemma sum_inv_succ_le_one_add_log (J : ℕ) :
    (∑ j ∈ Icc 1 J, (1 / (j + 1 : ℝ))) ≤ 1 + Real.log ((J + 1 : ℕ) : ℝ) := by
  have h1 : (∑ j ∈ Icc 1 J, (1 / (j + 1 : ℝ))) ≤ ∑ j ∈ Icc 1 J, (1 / (j : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
    have hjn : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hle : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    exact one_div_le_one_div_of_le hjn hle
  have h2 : (∑ j ∈ Icc 1 J, (1 / (j : ℝ))) ≤ ∑ i ∈ Icc 1 (J + 1), (1 / (i : ℝ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by norm_num) (by omega))
      (fun _ _ _ => by positivity)
  exact h1.trans (h2.trans (sum_inv_Icc_one_le_one_add_log (J + 1)))

/-- `2 ≤ log₂ n` for `n ≥ 4`. -/
lemma log2_ge_two_of_four_le {n : ℕ} (hn : 4 ≤ n) : 2 ≤ Nat.log 2 n := by
  have h := Nat.log_mono_right (b := 2) (by omega : 4 ≤ n)
  have h4 : Nat.log 2 4 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  simpa [h4] using h

/-- for a prime `p ≤ n`, `log₂ p` lies between `1` and `log₂ n`. -/
lemma log2_mem_Icc {n p : ℕ} (hp : p ∈ n.primesLE) : Nat.log 2 p ∈ Icc 1 (Nat.log 2 n) := by
  rw [mem_Icc]
  rw [Nat.mem_primesLE] at hp
  rcases hp with ⟨hple, hpp⟩
  constructor
  · have hp2 : 2 ≤ p := hpp.two_le
    exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (by omega : p ≠ 0)).2 (by simpa using hp2)
  · exact Nat.log_mono_right (b := 2) hple

/-- A prime `p` with `log₂ p = j` satisfies `p < 2^(j+1)`. -/
lemma lt_two_pow_succ_of_log2_eq {p j : ℕ} (h : Nat.log 2 p = j) : p < 2 ^ (j + 1) := by
  have h1 : p < 2 ^ (Nat.log 2 p).succ := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  rw [h, Nat.succ_eq_add_one] at h1
  exact h1

/-- `1 + log (log₂ n + 1) ≤ 3(1 + log log n)` for `n ≥ 4`. -/
lemma one_add_log_log2_succ_le_three {n : ℕ} (hn : 4 ≤ n) :
    1 + Real.log ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * (1 + Real.log (Real.log (n : ℝ))) := by
  have hlog2pos : 0 < Real.log 2 := log_two_pos
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
  have hinvle : (Real.log 2)⁻¹ ≤ 2 := log_two_inv_le_two
  have hJn : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    have hp : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have hcast : ((2 : ℝ) ^ Nat.log 2 n) ≤ (n : ℝ) := by
      have hp' : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp
      simpa using hp'
    have hmono : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) hcast
    have hL : Real.log ((2 : ℝ) ^ Nat.log 2 n) = (Nat.log 2 n : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    rw [hL] at hmono
    rwa [← le_div_iff₀ hlog2pos] at hmono
  have hJn' : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    calc
      (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := hJn
      _ = Real.log (n : ℝ) * (Real.log 2)⁻¹ := by ring
      _ ≤ Real.log (n : ℝ) * 2 := mul_le_mul_of_nonneg_left hinvle hlogpos
      _ = 2 * Real.log (n : ℝ) := by ring
  have hlogn1 : 1 ≤ Real.log (n : ℝ) := by
    have he4 : Real.exp 1 ≤ 4 := by linarith [exp_one_le_three]
    have hle : Real.log 4 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h4 : 1 ≤ Real.log 4 := by
      have hh : Real.log (Real.exp 1) ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) he4
      simpa using hh
    linarith
  have hlogn3 : (Nat.log 2 n : ℝ) + 1 ≤ 3 * Real.log (n : ℝ) := by
    have h1 : 1 ≤ Real.log (n : ℝ) := hlogn1
    nlinarith
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hmono2 : Real.log (((Nat.log 2 n + 1 : ℕ) : ℝ)) ≤ Real.log (3 * Real.log (n : ℝ)) := by
    have hnn : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * Real.log (n : ℝ) := by
      norm_num
      exact hlogn3
    have hpos2 : 0 < ((Nat.log 2 n + 1 : ℕ) : ℝ) := by positivity
    exact Real.log_le_log hpos2 hnn
  have hlog3 : Real.log (3 * Real.log (n : ℝ)) = Real.log 3 + Real.log (Real.log (n : ℝ)) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hlogpos)]
  have hlog3le2 : Real.log 3 ≤ 2 := by
    have he2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
      norm_num [Real.exp_nat_mul]
    have h3e : (3 : ℝ) ≤ Real.exp 2 := by
      rw [he2]
      have h25 : (5 : ℝ) / 2 ≤ Real.exp 1 := exp_one_ge_five_halves
      have hsq : ((5 : ℝ) / 2) ^ 2 ≤ (Real.exp 1) ^ 2 :=
        pow_le_pow_left₀ (a := (5 : ℝ) / 2) (by norm_num : 0 ≤ (5 : ℝ) / 2) h25 2
      norm_num at hsq
      nlinarith
    exact (Real.log_le_iff_le_exp (by norm_num : 0 < (3 : ℝ))).2 h3e
  calc
    1 + Real.log ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 1 + Real.log (3 * Real.log (n : ℝ)) := by
      gcongr
    _ = 1 + (Real.log 3 + Real.log (Real.log (n : ℝ))) := by rw [hlog3]
    _ ≤ 1 + (2 + Real.log (Real.log (n : ℝ))) := by linarith
    _ ≤ 3 * (1 + Real.log (Real.log (n : ℝ))) := by
      have hL : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg (by simpa using hlogn1)
      nlinarith

/-- natural harmonic-type bound on prime reciprocals, dyadic proof: for `n ≥ 4`,
`Σ_{p ≤ n} 1/p ≤ 100·(1 + log log n)`. -/
lemma primeRecips_nat_le (n : ℕ) (hn : 4 ≤ n) :
    primeRecips (n : ℝ) ≤ 100 * (1 + Real.log (Real.log (n : ℝ))) := by
  rw [primeRecips_nat]
  let J := Nat.log 2 n
  let A := n.primesLE
  have hmap : ∀ p ∈ A, Nat.log 2 p ∈ Icc 1 J := by
    intro p hp
    dsimp [A, J]
    exact log2_mem_Icc hp
  have hstep1 : (∑ p ∈ A, (1 / (p : ℝ))) ≤
      ∑ p ∈ A, (1 : ℝ) / (2 : ℝ) ^ Nat.log 2 p := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
    have hpow : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 (by omega : p ≠ 0)
    have hcast : ((2 : ℝ) ^ Nat.log 2 p) ≤ (p : ℝ) := by
      have hp' : ((2 ^ Nat.log 2 p : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpow
      simpa using hp'
    have hpowpos : 0 < (2 : ℝ) ^ Nat.log 2 p := by positivity
    exact one_div_le_one_div_of_le hpowpos hcast
  have hfib := Finset.sum_fiberwise_of_maps_to' (s := A) (t := Icc 1 J) hmap
    (f := fun j : ℕ => (1 : ℝ) / (2 : ℝ) ^ j)
  have hcount : ∀ j ∈ Icc 1 J,
      (((A.filter (fun p => Nat.log 2 p = j)).card : ℕ) : ℝ) ≤
        ((2 ^ (j + 1)).primesLE.card : ℝ) := by
    intro j hj
    exact_mod_cast (by
      refine Finset.card_le_card ?_
      intro p hp
      rw [mem_filter] at hp
      rcases hp with ⟨hpA, hlog⟩
      dsimp [A] at hpA
      rw [Nat.mem_primesLE] at hpA
      rcases hpA with ⟨hple, hpp⟩
      rw [Nat.mem_primesLE]
      constructor
      · exact le_of_lt (lt_two_pow_succ_of_log2_eq hlog)
      · exact hpp)
  have hfib_sum : ∀ j ∈ Icc 1 J,
      (∑ i ∈ A with Nat.log 2 i = j, (1 : ℝ) / (2 : ℝ) ^ j) ≤
        ((2 ^ (j + 1)).primesLE.card : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ j) := by
    intro j hj
    have h2pos : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num : 0 < (2 : ℝ)) j
    have hnonneg : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ j := div_nonneg (by norm_num) h2pos.le
    have hEq : (∑ i ∈ A with Nat.log 2 i = j, (1 : ℝ) / (2 : ℝ) ^ j)
        = (((A.filter (fun p => Nat.log 2 p = j)).card : ℕ) : ℝ) *
            ((1 : ℝ) / (2 : ℝ) ^ j) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hEq]
    exact mul_le_mul_of_nonneg_right (hcount j hj) hnonneg
  have hstep2 :
      ∑ p ∈ A, (1 : ℝ) / (2 : ℝ) ^ Nat.log 2 p ≤
        ∑ j ∈ Icc 1 J, ((1 : ℝ) / (2 : ℝ) ^ j) * ((2 ^ (j + 1)).primesLE.card : ℝ) := by
    have h1 : (∑ p ∈ A, (1 : ℝ) / (2 : ℝ) ^ Nat.log 2 p) =
        ∑ j ∈ Icc 1 J, ∑ i ∈ A with Nat.log 2 i = j, (1 : ℝ) / (2 : ℝ) ^ j := hfib.symm
    have h2 : (∑ j ∈ Icc 1 J, ∑ i ∈ A with Nat.log 2 i = j, (1 : ℝ) / (2 : ℝ) ^ j) ≤
        ∑ j ∈ Icc 1 J, ((2 ^ (j + 1)).primesLE.card : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ j) :=
      Finset.sum_le_sum hfib_sum
    have h3 : (∑ j ∈ Icc 1 J, ((2 ^ (j + 1)).primesLE.card : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ j)) =
        ∑ j ∈ Icc 1 J, ((1 : ℝ) / (2 : ℝ) ^ j) * ((2 ^ (j + 1)).primesLE.card : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_comm]
    exact h1.trans_le (h2.trans_eq h3)
  have hpi : ∀ j ∈ Icc 1 J,
      ((2 ^ (j + 1)).primesLE.card : ℝ) ≤
        (2 * Real.log 4 + 1) * (2 : ℝ) ^ (j + 1) / Real.log ((2 : ℝ) ^ (j + 1)) := by
    intro j hj
    have hnat : 2 ≤ 2 ^ (j + 1) := by
      have hp : (2 : ℕ) ^ 1 ≤ (2 : ℕ) ^ (j + 1) :=
        pow_le_pow_right₀ (a := (2 : ℕ)) (by norm_num : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ j + 1)
      simpa using hp
    have hpi := pi_upper_log_nat (2 ^ (j + 1)) hnat
    have hpe : ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := by
      rw [Nat.cast_pow]
      norm_num
    rwa [hpe] at hpi
  have hsum1 : (∑ j ∈ Icc 1 J,
      ((1 : ℝ) / (2 : ℝ) ^ j) * ((2 ^ (j + 1)).primesLE.card : ℝ)) ≤
        ∑ j ∈ Icc 1 J, (1 : ℝ) / (2 : ℝ) ^ j *
          ((2 * Real.log 4 + 1) * (2 : ℝ) ^ (j + 1) /
            Real.log ((2 : ℝ) ^ (j + 1))) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_left (hpi j hj) (by positivity)
  have htwo : ∀ j ∈ Icc 1 J, (2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ j = 2 := by
    intro j hj
    rw [pow_succ]
    field_simp
  have hlog : ∀ j ∈ Icc 1 J, Real.log ((2 : ℝ) ^ (j + 1)) = (j + 1 : ℝ) * Real.log 2 := by
    intro j hj
    rw [Real.log_pow]
    norm_num
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  have hterm_eq : ∀ j ∈ Icc 1 J,
      (1 : ℝ) / (2 : ℝ) ^ j * ((2 * Real.log 4 + 1) * (2 : ℝ) ^ (j + 1) /
          Real.log ((2 : ℝ) ^ (j + 1))) =
        (2 * Real.log 4 + 1) * 2 / Real.log 2 * (1 / (j + 1 : ℝ)) := by
    intro j hj
    calc
      (1 : ℝ) / (2 : ℝ) ^ j * ((2 * Real.log 4 + 1) * (2 : ℝ) ^ (j + 1) /
          Real.log ((2 : ℝ) ^ (j + 1)))
          = (1 : ℝ) / (2 : ℝ) ^ j * ((2 * Real.log 4 + 1) * (2 : ℝ) ^ (j + 1) /
              ((j + 1 : ℝ) * Real.log 2)) := by rw [hlog j hj]
      _ = (2 * Real.log 4 + 1) * 2 / Real.log 2 * (1 / (j + 1 : ℝ)) := by
            rw [pow_succ]
            field_simp [hlog2]
  have hsumEq : (∑ j ∈ Icc 1 J,
      (1 : ℝ) / (2 : ℝ) ^ j * ((2 * Real.log 4 + 1) * (2 : ℝ) ^ (j + 1) /
          Real.log ((2 : ℝ) ^ (j + 1)))) =
      (2 * Real.log 4 + 1) * 2 / Real.log 2 * (∑ j ∈ Icc 1 J, (1 / (j + 1 : ℝ))) := by
    calc
      (∑ j ∈ Icc 1 J,
          (1 : ℝ) / (2 : ℝ) ^ j * ((2 * Real.log 4 + 1) * (2 : ℝ) ^ (j + 1) /
            Real.log ((2 : ℝ) ^ (j + 1))))
          = ∑ j ∈ Icc 1 J, (2 * Real.log 4 + 1) * 2 / Real.log 2 * (1 / (j + 1 : ℝ)) := by
            exact Finset.sum_congr rfl (by intro j hj; exact hterm_eq j hj)
      _ = (2 * Real.log 4 + 1) * 2 / Real.log 2 * (∑ j ∈ Icc 1 J, (1 / (j + 1 : ℝ))) := by
            rw [Finset.mul_sum]
  have hsmall : (∑ j ∈ Icc 1 J, (1 / (j + 1 : ℝ))) ≤ 1 + Real.log ((J + 1 : ℕ) : ℝ) := by
    simpa [J] using sum_inv_succ_le_one_add_log (Nat.log 2 n)
  have hJlog : 1 + Real.log ((J + 1 : ℕ) : ℝ) ≤ 3 * (1 + Real.log (Real.log (n : ℝ))) := by
    dsimp [J]
    exact one_add_log_log2_succ_le_three hn
  have hfac : 0 ≤ (2 * Real.log 4 + 1) * 2 / Real.log 2 := by positivity
  have hCfinal : (2 * Real.log 4 + 1) * 2 / Real.log 2 * 3 ≤ 100 := by
    have hC1 : (2 * Real.log 4 + 1) ≤ 4 := pi_const_le_four
    have hinv : (Real.log 2)⁻¹ ≤ 2 := log_two_inv_le_two
    have hprod : (2 * Real.log 4 + 1) * (Real.log 2)⁻¹ ≤ 8 := by
      have hnonneg1 : 0 ≤ (Real.log 2)⁻¹ := by positivity
      have hm := mul_le_mul hC1 hinv hnonneg1 (by norm_num : 0 ≤ (4 : ℝ))
      norm_num at hm
      exact hm
    calc
      (2 * Real.log 4 + 1) * 2 / Real.log 2 * 3 = (2 * Real.log 4 + 1) * 6 * (Real.log 2)⁻¹ := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ 48 := by
        nlinarith [hprod]
      _ ≤ 100 := by norm_num
  calc
    (∑ p ∈ A, (1 / (p : ℝ))) ≤ ∑ p ∈ A, (1 : ℝ) / (2 : ℝ) ^ Nat.log 2 p := hstep1
    _ ≤ (2 * Real.log 4 + 1) * 2 / Real.log 2 * (∑ j ∈ Icc 1 J, (1 / (j + 1 : ℝ))) := by
      exact hstep2.trans (hsum1.trans_eq hsumEq)
    _ ≤ (2 * Real.log 4 + 1) * 2 / Real.log 2 * (3 * (1 + Real.log (Real.log (n : ℝ)))) := by
      refine mul_le_mul_of_nonneg_left ?_ hfac
      exact hsmall.trans hJlog
    _ ≤ 100 * (1 + Real.log (Real.log (n : ℝ))) := by
      have hL : 0 ≤ Real.log (Real.log (n : ℝ)) := by
        have h1 : 1 ≤ Real.log (n : ℝ) := by
          have hle : Real.log 4 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
          have he4 : Real.exp 1 ≤ 4 := by linarith [exp_one_le_three]
          have h4 : 1 ≤ Real.log 4 := by
            have hh : Real.log (Real.exp 1) ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) he4
            simpa using hh
          linarith
        exact Real.log_nonneg h1
      nlinarith

/-- real version: for `Y ≥ 4`, `Σ_{p ≤ Y} 1/p ≤ 100·(1 + log log Y)`. -/
lemma primeRecips_le (Y : ℝ) (hY : 4 ≤ Y) :
    primeRecips Y ≤ 100 * (1 + Real.log (Real.log Y)) := by
  have hnf : 4 ≤ ⌊Y⌋₊ := Nat.le_floor hY
  have hn := primeRecips_nat_le ⌊Y⌋₊ hnf
  have hEq : primeRecips Y = primeRecips (⌊Y⌋₊ : ℝ) := by
    unfold primeRecips
    rw [Nat.floor_natCast]
  rw [hEq]
  have hmono : Real.log (Real.log (⌊Y⌋₊ : ℝ)) ≤ Real.log (Real.log Y) := by
    have hle1 : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
    have hlog1 : Real.log (⌊Y⌋₊ : ℝ) ≤ Real.log Y :=
      Real.log_le_log (by positivity) hle1
    have hpos2 : 0 < Real.log (⌊Y⌋₊ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < ⌊Y⌋₊))
    have hpos3 : 0 < Real.log Y := Real.log_pos (by linarith : 1 < Y)
    exact Real.log_le_log hpos2 hlog1
  exact hn.trans (by
    have hL : 0 ≤ Real.log (Real.log (⌊Y⌋₊ : ℝ)) := by
      have h1 : 1 ≤ Real.log (⌊Y⌋₊ : ℝ) := by
        have hcast : (4 : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hnf
        have hle : Real.log 4 ≤ Real.log (⌊Y⌋₊ : ℝ) := Real.log_le_log (by norm_num) hcast
        have he4 : Real.exp 1 ≤ 4 := by linarith [exp_one_le_three]
        have h4 : 1 ≤ Real.log 4 := by
          have hh : Real.log (Real.exp 1) ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) he4
          simpa using hh
        linarith
      exact Real.log_nonneg h1
    have hpos : 0 ≤ 1 + Real.log (Real.log (⌊Y⌋₊ : ℝ)) := by linarith
    nlinarith)

end Harmonic








private lemma List.two_pow_length_le_prod {l : List ℕ} (h : ∀ x ∈ l, 2 ≤ x) :
    2 ^ l.length ≤ l.prod := by
  induction l with
  | nil => norm_num
  | cons x t ih =>
      have hx : 2 ≤ x := h x (by simp)
      have ht : ∀ y ∈ t, 2 ≤ y := fun y hy => h y (by simp [hy])
      have hprod : 0 < t.prod := by
        refine List.prod_pos ?_
        intro y hy
        have hyy : 2 ≤ y := ht y hy
        omega
      calc
        2 ^ (x :: t).length = 2 * 2 ^ t.length := by
          rw [List.length_cons, pow_succ]
          ring
        _ ≤ x * t.prod := Nat.mul_le_mul hx (ih ht)
        _ = (x :: t).prod := by simp

lemma two_pow_le_of_cardFactors_eq {m k : ℕ} (hk : 1 ≤ k)
    (h : ArithmeticFunction.cardFactors m = k) : 2 ^ k ≤ m := by
  have hm0 : m ≠ 0 := by
    intro hm0
    simp [hm0] at h
    omega
  have hlen : m.primeFactorsList.length = k := by
    rw [ArithmeticFunction.cardFactors_apply] at h
    exact h
  have hall : ∀ x ∈ m.primeFactorsList, 2 ≤ x := by
    intro x hx
    exact (Nat.prime_of_mem_primeFactorsList hx).two_le
  calc
    2 ^ k = 2 ^ m.primeFactorsList.length := by rw [hlen]
    _ ≤ m.primeFactorsList.prod := List.two_pow_length_le_prod hall
    _ = m := Nat.prod_primeFactorsList hm0

lemma two_le_iff_one_le_cardFactors (m : ℕ) : 2 ≤ m ↔ 1 ≤ ArithmeticFunction.cardFactors m := by
  constructor
  · intro hm
    have : 1 < m := by omega
    have hp : 0 < ArithmeticFunction.cardFactors m :=
      (ArithmeticFunction.cardFactors_pos_iff_one_lt).2 this
    omega
  · intro h
    by_contra hm
    have hmle : m ≤ 1 := by omega
    rcases lt_or_eq_of_le hmle with hlt | heq
    · have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;> simp at h
    · subst m
      simp at h

/-- For `p` prime dividing `m` with `Ω m = k + 1`, `Ω(m/p) = k`. -/
lemma cardFactors_div_of_prime_dvd {m p k : ℕ} (hp : Nat.Prime p) (hd : p ∣ m)
    (h : ArithmeticFunction.cardFactors m = k + 1) :
    ArithmeticFunction.cardFactors (m / p) = k := by
  rcases hd with ⟨c, hc⟩
  have hp0 : p ≠ 0 := Nat.Prime.ne_zero hp
  have hc0 : c ≠ 0 := by
    intro hc0
    have hm0 : m = 0 := by
      calc m = p * c := hc
           _ = 0 := by simp [hc0]
    simp [hm0] at h
  have hΩc : ArithmeticFunction.cardFactors c = k := by
    have hΩ : ArithmeticFunction.cardFactors m = 1 + ArithmeticFunction.cardFactors c := by
      calc
        ArithmeticFunction.cardFactors m = ArithmeticFunction.cardFactors (p * c) := by rw [hc]
        _ = ArithmeticFunction.cardFactors p + ArithmeticFunction.cardFactors c :=
          ArithmeticFunction.cardFactors_mul hp0 hc0
        _ = 1 + ArithmeticFunction.cardFactors c := by
          simp [ArithmeticFunction.cardFactors_apply_prime hp]
    omega
  have hcq : c = m / p := by
    exact Nat.eq_div_of_mul_eq_right hp0 hc.symm
  rwa [hcq] at hΩc

/-- The smallest prime factor `p` of an `(k+1)`-almost-prime satisfies `p² ≤ m`. -/
lemma minFac_sq_le_of_cardFactors {m k : ℕ} (hk : 1 ≤ k)
    (h : ArithmeticFunction.cardFactors m = k + 1) : m.minFac * m.minFac ≤ m := by
  have hmn1 : m ≠ 1 := by
    intro hmn1
    simp [hmn1] at h
  have hprim : Nat.Prime m.minFac := Nat.minFac_prime hmn1
  have hdv : m.minFac ∣ m := Nat.minFac_dvd m
  rcases hdv with ⟨c, hc⟩
  have hp0 : m.minFac ≠ 0 := Nat.Prime.ne_zero hprim
  have hc0 : c ≠ 0 := by
    intro hc0
    have hm0 : m = 0 := by
      calc m = m.minFac * c := hc
           _ = 0 := by simp [hc0]
    -- m=0: Ωm=0 ≠ k+1
    simp [hm0] at h
  have hΩc : ArithmeticFunction.cardFactors c = k := by
    have hΩ : ArithmeticFunction.cardFactors m =
        1 + ArithmeticFunction.cardFactors c := by
      calc
        ArithmeticFunction.cardFactors m = ArithmeticFunction.cardFactors (m.minFac * c) :=
          congrArg ArithmeticFunction.cardFactors hc
        _ = ArithmeticFunction.cardFactors m.minFac + ArithmeticFunction.cardFactors c :=
          ArithmeticFunction.cardFactors_mul hp0 hc0
        _ = 1 + ArithmeticFunction.cardFactors c := by
          simp [ArithmeticFunction.cardFactors_apply_prime hprim]
    omega
  have hc2 : 2 ≤ c := (two_le_iff_one_le_cardFactors c).2 (by omega)
  have hcD : c ∣ m := by
    refine ⟨m.minFac, ?_⟩
    calc
      m = m.minFac * c := hc
      _ = c * m.minFac := by rw [mul_comm]
  have hpc : m.minFac ≤ c := Nat.minFac_le_of_dvd hc2 hcD
  have hsq : m.minFac * m.minFac ≤ m.minFac * c := Nat.mul_le_mul_left m.minFac hpc
  rwa [hc.symm] at hsq

/-- The number of `m ≤ X` with `Ω m = k` (naturals `m`). -/
noncomputable def AP (k : ℕ) (X : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊X⌋₊).filter (fun m : ℕ => ArithmeticFunction.cardFactors m = k)).card

lemma AP_mono {k : ℕ} {X Y : ℝ} (hXY : X ≤ Y) : AP k X ≤ AP k Y := by
  unfold AP
  have hf : ⌊X⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono hXY
  exact Finset.card_le_card (by
    intro m hm
    simp only [mem_filter, mem_Icc] at hm ⊢
    exact ⟨⟨hm.1.1, le_trans hm.1.2 (by exact_mod_cast hf)⟩, hm.2⟩)

/-- `Ω m = k + 1` is impossible when `m < 2^(k+1)`. -/
lemma cardFactors_eq_impossible_of_lt {m k : ℕ} (h : ArithmeticFunction.cardFactors m = k)
    (hm : m < 2 ^ k) (hk : 0 < k) : False := by
  have hle : 2 ^ k ≤ m := two_pow_le_of_cardFactors_eq hk h
  omega

/-- `AP k X = 0` for `X < 2^k` when `k ≥ 1`. -/
lemma AP_eq_zero_of_lt {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX0 : 0 ≤ X) (hX : X < 2 ^ k) : AP k X = 0 := by
  unfold AP
  rw [Finset.card_eq_zero]
  ext m
  simp only [mem_filter, mem_Icc]
  constructor
  · intro hm
    have hpow : 2 ^ k ≤ m := two_pow_le_of_cardFactors_eq hk hm.2
    have hmX : (m : ℝ) ≤ X := by
      exact le_trans (by exact_mod_cast hm.1.2) (Nat.floor_le (by positivity : 0 ≤ X))
    have hpowR : (2 ^ k : ℝ) ≤ m := by exact_mod_cast hpow
    linarith
  · intro hmf
    simp at hmf

/-- `AP 1 X` counts the primes at most `X`. -/
lemma AP_one_eq_primeCount (X : ℝ) : AP 1 X = (⌊X⌋₊.primesLE).card := by
  unfold AP
  congr 1
  ext m
  simp only [mem_filter, mem_Icc, Nat.mem_primesLE]
  constructor
  · intro h
    exact ⟨h.1.2, (ArithmeticFunction.cardFactors_eq_one_iff_prime).1 h.2⟩
  · intro h
    exact ⟨⟨(Nat.Prime.one_le h.2), h.1⟩, (ArithmeticFunction.cardFactors_eq_one_iff_prime).2 h.2⟩



/-- fiber bound: for a prime `p`, the numbers `m ≤ X` with `Ω m = k+1` and `p ∣ m`
are at most `AP k (X/p)` in number. -/
lemma AP_fiber_le {k : ℕ} {X : ℝ} (hX0 : 0 ≤ X) {p : ℕ} (hp : Nat.Prime p) :
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun m : ℕ => Ω m = k + 1 ∧ p ∣ m)).card : ℕ) ≤
      AP k (X / (p : ℝ)) := by
  refine Finset.card_le_card_of_injOn (fun m : ℕ => m / p) ?_ ?_
  · -- MapsTo: image in (Icc 1 ⌊X/p⌋₊).filter Ω=k
    intro m hm
    rw [Finset.mem_coe] at hm ⊢
    simp at hm ⊢
    rcases hm with ⟨⟨hm1, hmX⟩, hmΩ, hpd⟩
    have hqΩ : Ω (m / p) = k := cardFactors_div_of_prime_dvd hp hpd hmΩ
    have hmq1 : 1 ≤ m / p := by
      have hp_le_m : p ≤ m := Nat.le_of_dvd (by omega : 0 < m) hpd
      exact (Nat.le_div_iff_mul_le (Nat.Prime.pos hp)).2 (by simpa using hp_le_m)
    have hmq : m / p ≤ ⌊X / (p : ℝ)⌋₊ := by
      have hmXc : (m : ℝ) ≤ X := by
        exact le_trans (by exact_mod_cast hmX) (Nat.floor_le hX0)
      have hle1 : ((m / p : ℕ) : ℝ) ≤ ((m : ℕ) : ℝ) / ((p : ℕ) : ℝ) := by
        exact Nat.cast_div_le
      have hle2 : (m : ℝ) / (p : ℝ) ≤ X / (p : ℝ) := by
        exact div_le_div_of_nonneg_right hmXc (by positivity : 0 ≤ (p : ℝ))
      exact Nat.le_floor (le_trans hle1 hle2)
    exact ⟨⟨hmq1, hmq⟩, hqΩ⟩
  · -- injectivity
    intro m₁ h₁ m₂ h₂ hdiv
    simp at h₁ h₂
    have hd1 : p ∣ m₁ := h₁.2.2
    have hd2 : p ∣ m₂ := h₂.2.2
    have hd : m₁ / p = m₂ / p := by simpa using hdiv
    calc
      m₁ = p * (m₁ / p) := (Nat.mul_div_cancel' hd1).symm
      _ = p * (m₂ / p) := by rw [hd]
      _ = m₂ := Nat.mul_div_cancel' hd2

/-- Real-variable decomposition: every `(k+1)`-almost-prime `m ≤ X` has a prime
factor `p ≤ √X`, and with `m = p·m'` we have `Ω m' = k`, `m' ≤ X/p`.
Hence `AP (k+1) X ≤ Σ_{p ≤ √X} AP k (X/p)`. -/
lemma AP_succ_le_sum_primes {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX0 : 0 ≤ X) :
    AP (k + 1) X ≤ ∑ p ∈ ⌊√X⌋₊.primesLE, AP k (X / (p : ℝ)) := by
  have hSU : ∀ m, m ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun m : ℕ => Ω m = k + 1) → m ∈
      (⌊√X⌋₊.primesLE).biUnion (fun p : ℕ =>
        (Finset.Icc 1 ⌊X⌋₊).filter (fun m : ℕ => Ω m = k + 1 ∧ p ∣ m)) := by
    intro m hmS
    simp at hmS
    have hΩ : Ω m = k + 1 := hmS.2
    have hmn1 : m ≠ 1 := by
      intro hmn1
      rw [hmn1] at hΩ
      simp at hΩ
    have hp : Nat.Prime m.minFac := Nat.minFac_prime hmn1
    have hpp : m.minFac * m.minFac ≤ m := minFac_sq_le_of_cardFactors hk hΩ
    have hpm : (m.minFac : ℝ) ≤ Real.sqrt X := by
      have hmX : (m : ℝ) ≤ X := by
        exact le_trans (by exact_mod_cast hmS.1.2) (Nat.floor_le hX0)
      have hppR : ((m.minFac : ℝ) ^ 2) ≤ X := by
        have h1 : ((m.minFac : ℝ) * (m.minFac : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hpp
        have h1' : ((m.minFac : ℝ) ^ 2) ≤ (m : ℝ) := by simpa [pow_two] using h1
        exact le_trans h1' hmX
      exact (Real.le_sqrt (by positivity : 0 ≤ (m.minFac : ℝ)) hX0).2 hppR
    have hp_floor : m.minFac ≤ ⌊√X⌋₊ := Nat.le_floor hpm
    have hp_mem : m.minFac ∈ ⌊√X⌋₊.primesLE := by
      rw [Nat.mem_primesLE]
      exact ⟨hp_floor, hp⟩
    rw [Finset.mem_biUnion]
    refine ⟨m.minFac, hp_mem, ?_⟩
    simp [hΩ, hmS.1, Nat.minFac_dvd m]
  calc
    AP (k + 1) X ≤ ((⌊√X⌋₊.primesLE).biUnion (fun p : ℕ =>
        (Finset.Icc 1 ⌊X⌋₊).filter (fun m : ℕ => Ω m = k + 1 ∧ p ∣ m))).card := by
      unfold AP
      exact Finset.card_le_card hSU
    _ ≤ ∑ p ∈ ⌊√X⌋₊.primesLE,
        ((Finset.Icc 1 ⌊X⌋₊).filter (fun m : ℕ => Ω m = k + 1 ∧ p ∣ m)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ p ∈ ⌊√X⌋₊.primesLE, AP k (X / (p : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro p hp_mem
      have hp : Nat.Prime p := (Nat.mem_primesLE.mp hp_mem).2
      have hps : (p : ℝ) ≤ Real.sqrt X := by
        have hple : p ≤ ⌊√X⌋₊ := (Nat.mem_primesLE.mp hp_mem).1
        have hc : (p : ℝ) ≤ (⌊√X⌋₊ : ℝ) := by exact_mod_cast hple
        exact hc.trans (Nat.floor_le (Real.sqrt_nonneg X))
      exact AP_fiber_le hX0 hp


section Levels

/-! ## The induction over the number of prime factors

We prove, for every `k ≥ 1`, the bound
`AP k X ≤ C·X·(log log X)^(k-1)/log X` for all `X ≥ 3`.
-/

/-- `log log X ≥ 1/10` for `X ≥ 4`. -/
lemma loglog_ge_one_tenth {X : ℝ} (hX : 4 ≤ X) : (1 : ℝ) / 10 ≤ Real.log (Real.log X) := by
  have hX1 : 1 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos hX1
  have hle1 : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hle2 : Real.log (Real.log 4) ≤ Real.log (Real.log X) := Real.log_le_log hlog4pos hle1
  exact le_trans log_log_four_ge hle2

/-- `log X ≤ 4` for `0 < X ≤ 16`. -/
lemma log_le_four_of_le_sixteen {X : ℝ} (hX0 : 0 < X) (hX : X ≤ 16) : Real.log X ≤ 4 := by
  have hle : Real.log X ≤ Real.log 16 := Real.log_le_log hX0 hX
  exact le_trans hle log_sixteen_le_four

/-- `√X ≥ 4` for `X ≥ 16`. -/
lemma sqrt_ge_four_of_sixteen {X : ℝ} (hX : 16 ≤ X) : 4 ≤ Real.sqrt X := by
  rw [Real.le_sqrt (by norm_num) (by linarith : 0 ≤ X)]
  norm_num
  linarith

/-- `X / p ≥ 3` for `16 ≤ X` and prime `p ≤ √X`. -/
lemma div_prime_sqrt_ge_three {X : ℝ} (hX : 16 ≤ X) (p : ℕ)
    (hp : p ∈ ⌊√X⌋₊.primesLE) : 3 ≤ X / (p : ℝ) := by
  have hppos : 0 < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos (Nat.mem_primesLE.mp hp).2)
  have hple : (p : ℝ) ≤ Real.sqrt X := by
    have h1 : p ≤ ⌊√X⌋₊ := (Nat.mem_primesLE.mp hp).1
    have hc : (p : ℝ) ≤ (⌊√X⌋₊ : ℝ) := by exact_mod_cast h1
    exact hc.trans (Nat.floor_le (Real.sqrt_nonneg X))
  have hdiv : Real.sqrt X ≤ X / (p : ℝ) := by
    rw [le_div_iff₀ hppos]
    have h2 : Real.sqrt X * Real.sqrt X = X := by
      simpa [pow_two] using Real.sq_sqrt (by linarith : 0 ≤ X)
    exact (mul_le_mul_of_nonneg_left hple (Real.sqrt_nonneg X)).trans_eq h2
  have h4 : 4 ≤ X / (p : ℝ) := le_trans (sqrt_ge_four_of_sixteen hX) hdiv
  linarith

/-- `X/p ≤ X` for `p ≥ 1` and `X ≥ 0`. -/
lemma div_le_self_of_one_le {X : ℝ} (hX0 : 0 ≤ X) (p : ℕ) (hp : 1 ≤ p) : X / (p : ℝ) ≤ X := by
  have hppos : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  rw [div_le_iff₀ hppos]
  have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  nlinarith [mul_le_mul_of_nonneg_left h1 hX0]

/-- monotonicity of `log log` on arguments at least `3`. -/
lemma loglog_le_loglog {a b : ℝ} (ha3 : 3 ≤ a) (hab : a ≤ b) : Real.log (Real.log a) ≤ Real.log (Real.log b) := by
  have hlogpos_a : 0 < Real.log a := Real.log_pos (by linarith : 1 < a)
  have hlogpos_b : 0 < Real.log b := by
    have : 1 < b := by linarith
    exact Real.log_pos this
  have hle : Real.log a ≤ Real.log b := Real.log_le_log (by linarith : 0 < a) hab
  exact Real.log_le_log hlogpos_a hle

/-- `log log a ≥ 0` for `a ≥ 3`. -/
lemma loglog_nonneg_of_three_le {a : ℝ} (ha : 3 ≤ a) : 0 ≤ Real.log (Real.log a) := by
  have h : 1 ≤ Real.log a := by
    have h1 : Real.log 3 ≤ Real.log a := Real.log_le_log (by norm_num) ha
    have h3 : 1 ≤ Real.log 3 := by
      have he : Real.exp 1 ≤ 3 := by linarith [exp_one_le_three]
      have hh : Real.log (Real.exp 1) ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) he
      simpa using hh
    linarith
  exact Real.log_nonneg h

/-- `AP k X ≤ ⌊X⌋₊`. -/
lemma AP_le_floor {k : ℕ} {X : ℝ} : (AP k X : ℝ) ≤ ⌊X⌋₊ := by
  unfold AP
  have hc : (((Icc 1 ⌊X⌋₊).filter (fun m : ℕ => ArithmeticFunction.cardFactors m = k)).card : ℕ) ≤ ⌊X⌋₊ := by
    calc
      (((Icc 1 ⌊X⌋₊).filter (fun m : ℕ => ArithmeticFunction.cardFactors m = k)).card : ℕ)
          ≤ ((Icc 1 ⌊X⌋₊).card : ℕ) := Finset.card_le_card (Finset.filter_subset _ _)
      _ = ⌊X⌋₊ := by rw [Nat.card_Icc]; omega
  exact_mod_cast hc

/-- `AP k X ≤ X` for `X ≥ 0`. -/
lemma AP_le_real {k : ℕ} {X : ℝ} (hX0 : 0 ≤ X) : (AP k X : ℝ) ≤ X := by
  have h1 : (AP k X : ℝ) ≤ (⌊X⌋₊ : ℝ) := AP_le_floor
  exact h1.trans (Nat.floor_le hX0)

/-- base level `k = 1`: the prime bound. -/
lemma level_one_bound : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
    AP 1 X ≤ C * X * (Real.log (Real.log X)) ^ (1 - 1) / Real.log X := by
  refine ⟨(2 * Real.log 4 + 1), pi_const_pos, ?_⟩
  intro X hX
  rw [AP_one_eq_primeCount]
  rw [pow_zero, mul_one]
  exact pi_upper_log_real X (by linarith)

/-- trivial bound on a level below 16 (used for levels two and three). -/
lemma bound_small_level {k : ℕ} {X : ℝ} (hX4 : 4 ≤ X) (hX16 : X ≤ 16) {C : ℝ}
    (hCpos : 0 ≤ C) (hC : 4 ≤ C * ((1 : ℝ) / 10) ^ k) :
    (AP (k + 1) X : ℝ) ≤ C * X * (Real.log (Real.log X)) ^ k / Real.log X := by
  have hXpos : 0 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith : 1 < X)
  have h1 : (AP (k + 1) X : ℝ) ≤ X := AP_le_real (by linarith)
  have hXle : X ≤ C * X * (Real.log (Real.log X)) ^ k / Real.log X := by
    have hL : (1 : ℝ) / 10 ≤ Real.log (Real.log X) := loglog_ge_one_tenth hX4
    have hLnonneg : 0 ≤ Real.log (Real.log X) := by linarith
    have hlog4 : Real.log X ≤ 4 := log_le_four_of_le_sixteen hXpos hX16
    have hpow : ((1 : ℝ) / 10) ^ k ≤ (Real.log (Real.log X)) ^ k := by
      exact pow_le_pow_left₀ (a := (1 : ℝ) / 10) (by norm_num : 0 ≤ (1 : ℝ) / 10) hL k
    have hCk : 4 ≤ C * (Real.log (Real.log X)) ^ k := by
      have hc := mul_le_mul_of_nonneg_left hpow hCpos
      nlinarith
    have hmul : Real.log X ≤ C * (Real.log (Real.log X)) ^ k := by linarith
    rw [le_div_iff₀ hlogpos]
    calc
      X * Real.log X ≤ X * (C * (Real.log (Real.log X)) ^ k) := by
        exact mul_le_mul_of_nonneg_left hmul (by linarith : 0 ≤ X)
      _ = C * X * (Real.log (Real.log X)) ^ k := by ring
  exact h1.trans hXle

/-- The induction step (levels `k ≥ 1`), valid for `X ≥ 16`. -/
lemma level_step {k : ℕ} (hk : 1 ≤ k) {Ck : ℝ} (hCk : 0 < Ck)
    (hIH : ∀ X : ℝ, 3 ≤ X → AP k X ≤ Ck * X * (Real.log (Real.log X)) ^ (k - 1) / Real.log X) :
    ∀ X : ℝ, 16 ≤ X →
      AP (k + 1) X ≤ ((2 * 100) * 11 * Ck) * X * (Real.log (Real.log X)) ^ k / Real.log X := by
  intro X hX
  have hX0 : 0 ≤ X := by linarith
  have hX4 : 4 ≤ X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith : 1 < X)
  have hdecomp := AP_succ_le_sum_primes hk hX0
  have hL : (1 : ℝ) / 10 ≤ Real.log (Real.log X) := loglog_ge_one_tenth hX4
  have hLnonneg : 0 ≤ Real.log (Real.log X) := by linarith
  have hXsqrt : 4 ≤ Real.sqrt X := sqrt_ge_four_of_sixteen hX
  have hLLsqrt : Real.log (Real.log (Real.sqrt X)) ≤ Real.log (Real.log X) := by
    have hx1 : 1 ≤ X := by linarith
    have hxx : X ≤ X ^ 2 := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left hx1 hX0
    have hs : Real.sqrt X ≤ X := (Real.sqrt_le_iff).2 ⟨hX0, hxx⟩
    exact loglog_le_loglog (by linarith : 3 ≤ Real.sqrt X) hs
  have hsmall : (1 + Real.log (Real.log (Real.sqrt X))) ≤ 11 * Real.log (Real.log X) := by
    nlinarith
  have htop_nonneg : 0 ≤ 2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X := by
    have hpow : 0 ≤ (Real.log (Real.log X)) ^ (k - 1) := pow_nonneg hLnonneg _
    positivity
  have hfac : 0 ≤ 2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X / Real.log X := by
    exact div_nonneg htop_nonneg hlogpos.le
  have hterm : ∀ p ∈ ⌊√X⌋₊.primesLE,
      (AP k (X / (p : ℝ)) : ℝ) ≤ 2 * Ck * (X / (p : ℝ)) *
        (Real.log (Real.log X)) ^ (k - 1) / Real.log X := by
    intro p hp
    have hY : 3 ≤ X / (p : ℝ) := div_prime_sqrt_ge_three hX p hp
    have hYlogpos : 0 < Real.log (X / (p : ℝ)) := Real.log_pos (by linarith : 1 < X / (p : ℝ))
    have hIHp := hIH (X / (p : ℝ)) hY
    have hmonoL : Real.log (Real.log (X / (p : ℝ))) ≤ Real.log (Real.log X) := by
      have hle1 : X / (p : ℝ) ≤ X := div_le_self_of_one_le hX0 p (Nat.Prime.one_lt (Nat.mem_primesLE.mp hp).2).le
      exact loglog_le_loglog hY hle1
    have hLnonnegY : 0 ≤ Real.log (Real.log (X / (p : ℝ))) := loglog_nonneg_of_three_le hY
    have hpowL : (Real.log (Real.log (X / (p : ℝ)))) ^ (k - 1) ≤
        (Real.log (Real.log X)) ^ (k - 1) := by
      exact pow_le_pow_left₀ (a := Real.log (Real.log (X / (p : ℝ)))) hLnonnegY hmonoL (k - 1)
    have hdivlog : (1 : ℝ) / Real.log (X / (p : ℝ)) ≤ 2 / Real.log X := by
      have hppos : 0 < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos (Nat.mem_primesLE.mp hp).2)
      have hple : (p : ℝ) ≤ Real.sqrt X := by
        have h1 : p ≤ ⌊√X⌋₊ := (Nat.mem_primesLE.mp hp).1
        have hc : (p : ℝ) ≤ (⌊√X⌋₊ : ℝ) := by exact_mod_cast h1
        exact hc.trans (Nat.floor_le (Real.sqrt_nonneg X))
      have hsqrtle : Real.sqrt X ≤ X / (p : ℝ) := by
        rw [le_div_iff₀ hppos]
        have h2 : Real.sqrt X * Real.sqrt X = X := by
          simpa [pow_two] using Real.sq_sqrt (by linarith : 0 ≤ X)
        exact (mul_le_mul_of_nonneg_left hple (Real.sqrt_nonneg X)).trans_eq h2
      have hlogs : Real.log (Real.sqrt X) ≤ Real.log (X / (p : ℝ)) :=
        Real.log_le_log (by positivity : 0 < Real.sqrt X) hsqrtle
      have hloghalf : Real.log X / 2 ≤ Real.log (X / (p : ℝ)) := by
        have hsqrtlog : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt (by linarith : 0 ≤ X)
        rwa [hsqrtlog] at hlogs
      have hhalf : 0 < Real.log X / 2 := by positivity
      calc
        (1 : ℝ) / Real.log (X / (p : ℝ)) ≤ (1 : ℝ) / (Real.log X / 2) :=
          one_div_le_one_div_of_le hhalf hloghalf
        _ = 2 / Real.log X := by field_simp [hlogpos.ne']
    calc
      (AP k (X / (p : ℝ)) : ℝ) ≤ Ck * (X / (p : ℝ)) * (Real.log (Real.log (X / (p : ℝ)))) ^ (k - 1) /
          Real.log (X / (p : ℝ)) := hIHp
      _ = Ck * (X / (p : ℝ)) * (Real.log (Real.log (X / (p : ℝ)))) ^ (k - 1) *
          (1 / Real.log (X / (p : ℝ))) := by ring
      _ ≤ Ck * (X / (p : ℝ)) * (Real.log (Real.log X)) ^ (k - 1) * (2 / Real.log X) := by
            have hA : 0 ≤ Ck * (X / (p : ℝ)) := by positivity
            have hB : 0 ≤ Ck * (X / (p : ℝ)) * (Real.log (Real.log X)) ^ (k - 1) := by positivity
            have hrec : 0 ≤ (1 : ℝ) / Real.log (X / (p : ℝ)) :=
              div_nonneg (by norm_num) hYlogpos.le
            have hstep1 : Ck * (X / (p : ℝ)) * (Real.log (Real.log (X / (p : ℝ)))) ^ (k - 1) *
                (1 / Real.log (X / (p : ℝ))) ≤
                Ck * (X / (p : ℝ)) * (Real.log (Real.log X)) ^ (k - 1) *
                  (1 / Real.log (X / (p : ℝ))) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpowL hA) hrec
            exact hstep1.trans (mul_le_mul_of_nonneg_left hdivlog hB)
      _ = 2 * Ck * (X / (p : ℝ)) * (Real.log (Real.log X)) ^ (k - 1) / Real.log X := by ring
  have hdecompR : (AP (k + 1) X : ℝ) ≤
      ∑ p ∈ ⌊√X⌋₊.primesLE, (AP k (X / (p : ℝ)) : ℝ) := by
    have hcast_sum : ((∑ p ∈ ⌊√X⌋₊.primesLE, AP k (X / (p : ℝ)) : ℕ) : ℝ) =
        ∑ p ∈ ⌊√X⌋₊.primesLE, (AP k (X / (p : ℝ)) : ℝ) := by
      simp
    rw [← hcast_sum]
    exact_mod_cast hdecomp
  have hsum : (∑ p ∈ ⌊√X⌋₊.primesLE, (AP k (X / (p : ℝ)) : ℝ)) ≤
      ∑ p ∈ ⌊√X⌋₊.primesLE,
        2 * Ck * (X / (p : ℝ)) * (Real.log (Real.log X)) ^ (k - 1) / Real.log X := by
    exact Finset.sum_le_sum hterm
  have hsumEq : (∑ p ∈ ⌊√X⌋₊.primesLE,
        2 * Ck * (X / (p : ℝ)) * (Real.log (Real.log X)) ^ (k - 1) / Real.log X) =
      (2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X / Real.log X) *
        (∑ p ∈ ⌊√X⌋₊.primesLE, (1 / (p : ℝ))) := by
    calc
      (∑ p ∈ ⌊√X⌋₊.primesLE,
          2 * Ck * (X / (p : ℝ)) * (Real.log (Real.log X)) ^ (k - 1) / Real.log X)
          = ∑ p ∈ ⌊√X⌋₊.primesLE,
              (2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X / Real.log X) * (1 / (p : ℝ)) := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
      _ = (2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X / Real.log X) *
          (∑ p ∈ ⌊√X⌋₊.primesLE, (1 / (p : ℝ))) := by
            rw [Finset.mul_sum]
  have hprimeRecips : (∑ p ∈ ⌊√X⌋₊.primesLE, (1 / (p : ℝ))) = primeRecips (Real.sqrt X) := by
    rfl
  have hprimeBound : primeRecips (Real.sqrt X) ≤ 100 * (1 + Real.log (Real.log (Real.sqrt X))) :=
    primeRecips_le (Real.sqrt X) hXsqrt
  have hfac2 : 0 ≤ (2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X / Real.log X) := hfac
  have hCfin : (2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X / Real.log X) *
        (100 * (11 * Real.log (Real.log X))) ≤
      ((2 * 100) * 11 * Ck) * X * (Real.log (Real.log X)) ^ k / Real.log X := by
    have hkpow : (Real.log (Real.log X)) ^ k =
        (Real.log (Real.log X)) ^ (k - 1) * Real.log (Real.log X) := by
      rw [← pow_succ]
      congr 1
      omega
    have hEq : (2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X / Real.log X) *
          (100 * (11 * Real.log (Real.log X))) =
        ((2 * 100) * 11 * Ck) * X * (Real.log (Real.log X)) ^ k / Real.log X := by
      calc
        (2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X / Real.log X) *
            (100 * (11 * Real.log (Real.log X)))
            = 2 * Ck * X * ((Real.log (Real.log X)) ^ (k - 1) * Real.log (Real.log X)) * 100 * 11 /
                Real.log X := by ring
        _ = 2 * Ck * X * (Real.log (Real.log X)) ^ k * 100 * 11 / Real.log X := by rw [hkpow]
        _ = ((2 * 100) * 11) * Ck * X * (Real.log (Real.log X)) ^ k / Real.log X := by ring
    exact le_of_eq hEq
  calc
    (AP (k + 1) X : ℝ) ≤ (∑ p ∈ ⌊√X⌋₊.primesLE, (AP k (X / (p : ℝ)) : ℝ)) := hdecompR
    _ ≤ ∑ p ∈ ⌊√X⌋₊.primesLE,
        2 * Ck * (X / (p : ℝ)) * (Real.log (Real.log X)) ^ (k - 1) / Real.log X := hsum
    _ = (2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X / Real.log X) *
        primeRecips (Real.sqrt X) := by
          rw [hsumEq, hprimeRecips]
    _ ≤ (2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X / Real.log X) *
        (100 * (1 + Real.log (Real.log (Real.sqrt X)))) := by
          exact mul_le_mul_of_nonneg_left hprimeBound hfac2
    _ ≤ (2 * Ck * (Real.log (Real.log X)) ^ (k - 1) * X / Real.log X) *
        (100 * (11 * Real.log (Real.log X))) := by
          have hs100 : 100 * (1 + Real.log (Real.log (Real.sqrt X))) ≤
              100 * (11 * Real.log (Real.log X)) := by
            exact mul_le_mul_of_nonneg_left hsmall (by norm_num)
          exact mul_le_mul_of_nonneg_left hs100 hfac2
    _ ≤ ((2 * 100) * 11 * Ck) * X * (Real.log (Real.log X)) ^ k / Real.log X := hCfin


/-- the level multiplier `(2·100)·11` (from `level_step` and `primeRecips_le`). -/
def KK : ℝ := (2 * 100) * 11

/-- the base prime-count constant `2·log 4 + 1`. -/
def C1c : ℝ := 2 * Real.log 4 + 1

lemma KK_pos : 0 < KK := by norm_num [KK]

lemma C1c_pos : 0 < C1c := pi_const_pos

lemma C1c_ge_one : 1 ≤ C1c := by
  unfold C1c
  have h : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  nlinarith

/-- level-one claim with the explicit constant. -/
lemma level_one_prop (X : ℝ) (hX : 3 ≤ X) :
    AP 1 X ≤ C1c * X * (Real.log (Real.log X)) ^ (1 - 1) / Real.log X := by
  rw [AP_one_eq_primeCount]
  rw [pow_zero, mul_one]
  exact pi_upper_log_real X (by linarith)

/-- level-two claim with explicit constant `KK·C1c`. -/
lemma level_two_prop (X : ℝ) (hX : 3 ≤ X) :
    AP 2 X ≤ (KK * C1c) * X * (Real.log (Real.log X)) ^ (2 - 1) / Real.log X := by
  have hpow1 : (2 - 1 : ℕ) = 1 := by omega
  rw [hpow1]
  by_cases hX4 : 4 ≤ X
  · by_cases hX16 : X ≤ 16
    · -- X ∈ [4,16]: trivial bound
      have hCpos : 0 ≤ KK * C1c := le_of_lt (mul_pos KK_pos C1c_pos)
      have h40 : 40 ≤ KK * C1c := by
        dsimp [KK]
        have hC : 1 ≤ C1c := C1c_ge_one
        nlinarith
      have hC : 4 ≤ (KK * C1c) * ((1 : ℝ) / 10) ^ 1 := by
        rw [pow_one]
        nlinarith [h40]
      exact bound_small_level (k := 1) hX4 hX16 hCpos hC
    · -- X ≥ 16: induction step from level one
      have hX16' : 16 ≤ X := le_of_not_ge hX16
      have hstep := level_step (k := 1) (by omega : 1 ≤ 1) (Ck := C1c) C1c_pos level_one_prop
      have hst := hstep X hX16'
      have hK : ((2 * 100) * 11) * C1c = KK * C1c := by rfl
      rwa [hK] at hst
  · have hXlt : X < 4 := lt_of_not_ge hX4
    have hXlt' : X < (2 : ℝ) ^ 2 := by norm_num; exact hXlt
    have hAP : AP 2 X = 0 := AP_eq_zero_of_lt (by omega : 1 ≤ 2) (by linarith : 0 ≤ X) hXlt'
    rw [hAP]
    have hL : 0 ≤ Real.log (Real.log X) := loglog_nonneg_of_three_le hX
    have hlogpos : 0 < Real.log X := Real.log_pos (by linarith : 1 < X)
    have hK : 0 ≤ KK * C1c := le_of_lt (mul_pos KK_pos C1c_pos)
    have hXpos : 0 ≤ X := by linarith
    have hP : 0 ≤ (Real.log (Real.log X)) ^ 1 := pow_nonneg hL 1
    have hnum : 0 ≤ (KK * C1c) * X * (Real.log (Real.log X)) ^ 1 := by positivity
    have hR : 0 ≤ (KK * C1c) * X * (Real.log (Real.log X)) ^ 1 / Real.log X :=
      div_nonneg hnum hlogpos.le
    simpa using hR

/-- level-three claim with explicit constant `KK·(KK·C1c)`. -/
lemma level_three_prop (X : ℝ) (hX : 3 ≤ X) :
    AP 3 X ≤ (KK * (KK * C1c)) * X * (Real.log (Real.log X)) ^ (3 - 1) / Real.log X := by
  have hpow2 : (3 - 1 : ℕ) = 2 := by omega
  rw [hpow2]
  by_cases hX8 : 8 ≤ X
  · by_cases hX16 : X ≤ 16
    · have hCpos : 0 ≤ KK * (KK * C1c) :=
        le_of_lt (mul_pos KK_pos (mul_pos KK_pos C1c_pos))
      have h400 : 400 ≤ KK * (KK * C1c) := by
        dsimp [KK]
        have hC : 1 ≤ C1c := C1c_ge_one
        nlinarith
      have hC : 4 ≤ (KK * (KK * C1c)) * ((1 : ℝ) / 10) ^ 2 := by
        norm_num [pow_two]
        nlinarith [h400]
      exact bound_small_level (k := 2) (by linarith : 4 ≤ X) hX16 hCpos hC
    · have hX16' : 16 ≤ X := le_of_not_ge hX16
      have hC2pos : 0 < KK * C1c := mul_pos KK_pos C1c_pos
      have hstep := level_step (k := 2) (by omega : 1 ≤ 2) (Ck := KK * C1c) hC2pos level_two_prop
      have hst := hstep X hX16'
      have hK : ((2 * 100) * 11) * (KK * C1c) = KK * (KK * C1c) := by rfl
      rwa [hK] at hst
  · have hXlt : X < 8 := lt_of_not_ge hX8
    have hXlt' : X < (2 : ℝ) ^ 3 := by norm_num; exact hXlt
    have hAP : AP 3 X = 0 := AP_eq_zero_of_lt (by omega : 1 ≤ 3) (by linarith : 0 ≤ X) hXlt'
    rw [hAP]
    have hL : 0 ≤ Real.log (Real.log X) := loglog_nonneg_of_three_le hX
    have hlogpos : 0 < Real.log X := Real.log_pos (by linarith : 1 < X)
    have hK : 0 ≤ KK * (KK * C1c) := le_of_lt (mul_pos KK_pos (mul_pos KK_pos C1c_pos))
    have hXpos : 0 ≤ X := by linarith
    have hP : 0 ≤ (Real.log (Real.log X)) ^ 2 := pow_nonneg hL 2
    have hnum : 0 ≤ (KK * (KK * C1c)) * X * (Real.log (Real.log X)) ^ 2 := by positivity
    have hR : 0 ≤ (KK * (KK * C1c)) * X * (Real.log (Real.log X)) ^ 2 / Real.log X :=
      div_nonneg hnum hlogpos.le
    simpa using hR

/-- bound for every level at least three. -/
theorem level_bound_ge_three : ∀ (k : ℕ), 3 ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
    AP k X ≤ C * X * (Real.log (Real.log X)) ^ (k - 1) / Real.log X := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk2 : k = 2
      · subst k
        have hCpos : 0 < KK * (KK * C1c) := mul_pos KK_pos (mul_pos KK_pos C1c_pos)
        refine ⟨KK * (KK * C1c), hCpos, ?_⟩
        intro X hX
        have hp2 : (3 - 1 : ℕ) = 2 := by omega
        simpa [hp2] using level_three_prop X hX
      · have hk3 : 3 ≤ k := by omega
        have hprev := ih hk3
        rcases hprev with ⟨Ck, hCk, hprevProp⟩
        have hstep := level_step (k := k) (by omega : 1 ≤ k) (Ck := Ck) hCk hprevProp
        have hCpos : 0 < KK * Ck := mul_pos KK_pos hCk
        refine ⟨KK * Ck, hCpos, ?_⟩
        intro X hX
        have hke : (k + 1 - 1 : ℕ) = k := by omega
        rw [hke]
        by_cases hXlt : X < (2 : ℝ) ^ (k + 1)
        · have hAP : AP (k + 1) X = 0 :=
            AP_eq_zero_of_lt (by omega : 1 ≤ k + 1) (by linarith : 0 ≤ X) hXlt
          rw [hAP]
          have hL : 0 ≤ Real.log (Real.log X) := loglog_nonneg_of_three_le hX
          have hlogpos : 0 < Real.log X := Real.log_pos (by linarith : 1 < X)
          have hK : 0 ≤ KK * Ck := le_of_lt (mul_pos KK_pos hCk)
          have hXpos : 0 ≤ X := by linarith
          have hP : 0 ≤ (Real.log (Real.log X)) ^ k := pow_nonneg hL k
          have hnum : 0 ≤ (KK * Ck) * X * (Real.log (Real.log X)) ^ k := by positivity
          have hR : 0 ≤ (KK * Ck) * X * (Real.log (Real.log X)) ^ k / Real.log X :=
            div_nonneg hnum hlogpos.le
          simpa using hR
        · have hX16 : 16 ≤ X := by
            have hle : (2 : ℝ) ^ (k + 1) ≤ X := le_of_not_gt hXlt
            have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
              have hp : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ (k + 1) :=
                pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (by omega : 4 ≤ k + 1)
              norm_num at hp
              exact hp
            linarith
          exact hstep X hX16

/-- every level `k ≥ 1` has the desired bound. -/
theorem level_bound_all (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
    AP k X ≤ C * X * (Real.log (Real.log X)) ^ (k - 1) / Real.log X := by
  by_cases hk1 : k = 1
  · subst k
    exact level_one_bound
  · have hk2 : 2 ≤ k := by omega
    by_cases hk2' : k = 2
    · subst k
      have hCpos : 0 < KK * C1c := mul_pos KK_pos C1c_pos
      refine ⟨KK * C1c, hCpos, ?_⟩
      intro X hX
      have hp1 : (2 - 1 : ℕ) = 1 := by omega
      simpa [hp1] using level_two_prop X hX
    · have hk3 : 3 ≤ k := by omega
      exact level_bound_ge_three k hk3

/-- `AP k N` for a natural `N` is the number of `m ≤ N` with `Ω m = k`. -/
lemma AP_nat (k N : ℕ) : AP k (N : ℝ) =
    ((Finset.Icc 1 N).filter (fun m : ℕ => ArithmeticFunction.cardFactors m = k)).card := by
  unfold AP
  rw [Nat.floor_natCast]
/-- The almost-prime count bound: for a fixed `k ≥ 1` the number of `m ≤ N` with
`Ω m = k` is `O_C(k)(N·(log log N)^(k-1)/log N)`. -/
lemma card_Omega_eq_le (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      ((Finset.Icc 1 N).filter (fun m : ℕ => ArithmeticFunction.cardFactors m = k)).card
        ≤ C * (N : ℝ) * (Real.log (Real.log (N : ℝ))) ^ (k - 1) / Real.log (N : ℝ) := by
  rcases level_bound_all k hk with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hX : 3 ≤ (N : ℝ) := by exact_mod_cast hN
  have hb := hmain (N : ℝ) hX
  rwa [AP_nat] at hb


end Levels
end
end Commons.NumberTheory.ArithmeticFunction