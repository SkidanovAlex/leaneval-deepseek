import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.Complex.ExponentialBounds
import ChallengeDeps

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval
open FractionalExpectationThresholds

attribute [local instance] Classical.propDecidable

namespace Submission
namespace FET

universe u
variable {X : Type u} [Fintype X]

/-- The binomial upper tail is the probability that a `p`-random set has size at least `m`. -/
def binomTail (n m : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc m n, (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-! ## Proof of the binomial tail lower bound

The upper tail `binomTail n m p = ∑_{k=m}^{n} C(n,k) p^k (1-p)^{n-k}` is the probability
that `K ≥ m` for `K ~ Bin(n,p)`.  We prove the elementary Chernoff-type estimate

`∑_{k < m} C(n,k) p^k (1-p)^{n-k} ≤ 1/4` whenever `m ≤ np/2` and `np ≥ 12`,

by the moment-generating-function argument: for `t > 0` and `k < m`, the mass at `k` is
dominated by `e^{t(m-1-k)}` times itself; summing and extending to all `k ≤ n` gives
`P(K < m) ≤ e^{t(m-1)} (1 - p + p e^{-t})^n ≤ e^{t(m-1)} e^{-np(1-e^{-t})}` (using
`1 - x ≤ e^{-x}`).  With `t = 1`, `m ≤ np/2` and `np ≥ 12` the exponent is `≤ -11/5`,
and `e^{-11/5} ≤ 1/4`.
-/

/-- point mass `P(K = k)`, a single term of the binomial sums -/
private def bt (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-- Sum of all point masses is `(p + (1-p))^n = 1` (binomial theorem). -/
private lemma bt_sum_all (n : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (n + 1), bt n p k) = 1 := by
  have h := add_pow (x := p) (y := 1 - p) (n := n)
  calc
    (∑ k ∈ Finset.range (n + 1), bt n p k)
        = (∑ k ∈ Finset.range (n + 1), p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          unfold bt
          ring
    _ = (p + (1 - p)) ^ n := h.symm
    _ = 1 := by
      have hb : p + (1 - p) = 1 := by ring
      rw [hb, one_pow]

/-- Each point mass is nonnegative when `0 ≤ p ≤ 1`. -/
private lemma bt_nonneg (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ bt n p k := by
  unfold bt
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp0 k)) (pow_nonneg (by linarith) (n - k))

/-- `range (n+1)` splits as `range m ∪ Icc m n` when `m ≤ n`. -/
private lemma range_succ_eq_range_add_Icc (m n : ℕ) (hmn : m ≤ n) :
    Finset.range (n + 1) = Finset.range m ∪ Finset.Icc m n := by
  ext k
  constructor
  · intro hk
    have hk' : k ≤ n := by
      have : k < n + 1 := Finset.mem_range.mp hk
      omega
    by_cases hkm : k < m
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hkm))
    · have hmk : m ≤ k := by omega
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_Icc.mpr ⟨hmk, hk'⟩))
  · intro hk
    rw [Finset.mem_union] at hk
    rcases hk with hkm | hkcc
    · rw [Finset.mem_range] at hkm
      exact Finset.mem_range.mpr (by omega)
    · rw [Finset.mem_Icc] at hkcc
      exact Finset.mem_range.mpr (by omega)

/-- The total sum splits into the low tail (`k < m`) and the upper tail (`m ≤ k ≤ n`). -/
private lemma bt_sum_split (m n : ℕ) (p : ℝ) (hmn : m ≤ n) :
    (∑ k ∈ Finset.range (n + 1), bt n p k)
      = (∑ k ∈ Finset.range m, bt n p k) + (∑ k ∈ Finset.Icc m n, bt n p k) := by
  calc
    (∑ k ∈ Finset.range (n + 1), bt n p k)
        = (∑ k ∈ Finset.range m ∪ Finset.Icc m n, bt n p k) := by
          rw [range_succ_eq_range_add_Icc m n hmn]
    _ = (∑ k ∈ Finset.range m, bt n p k) + (∑ k ∈ Finset.Icc m n, bt n p k) := by
          rw [Finset.sum_union]
          rw [Finset.disjoint_left]
          intro k hk1 hk2
          simp only [Finset.mem_range] at hk1
          simp only [Finset.mem_Icc] at hk2
          omega

/-- `binomTail n m p = 1 - P(K < m)` (the complement identity). -/
private lemma binomTail_eq_one_sub_low (n m : ℕ) (p : ℝ) (hmn : m ≤ n) :
    binomTail n m p = 1 - (∑ k ∈ Finset.range m, bt n p k) := by
  have htail : (∑ k ∈ Finset.Icc m n, bt n p k) = binomTail n m p := by
    unfold binomTail bt
    rfl
  have hmain : (∑ k ∈ Finset.range m, bt n p k) + binomTail n m p = 1 := by
    calc
      (∑ k ∈ Finset.range m, bt n p k) + binomTail n m p
          = (∑ k ∈ Finset.range m, bt n p k) + (∑ k ∈ Finset.Icc m n, bt n p k) := by rw [htail]
      _ = (∑ k ∈ Finset.range (n + 1), bt n p k) := by
            rw [bt_sum_split m n p hmn]
      _ = 1 := bt_sum_all n p
  linarith

/-- `exp (-k) = (exp (-1))^k` for `k : ℕ`. -/
private lemma exp_neg_nat (k : ℕ) : Real.exp (-(k : ℝ)) = Real.exp (-1) ^ k := by
  rw [← Real.exp_nat_mul (-1) k]
  congr 1
  ring

/-- Moment-generating-function identity: `𝔼[e^{-K}] = (1 - p + p e^{-1})^n`. -/
private lemma mgf_sum_eq (n : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (n + 1), Real.exp (-(k : ℝ)) * bt n p k)
      = (1 - p + p * Real.exp (-1)) ^ n := by
  have h := add_pow (x := p * Real.exp (-1)) (y := 1 - p) (n := n)
  calc
    (∑ k ∈ Finset.range (n + 1), Real.exp (-(k : ℝ)) * bt n p k)
        = (∑ k ∈ Finset.range (n + 1), (p * Real.exp (-1)) ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have he : Real.exp (-(k : ℝ)) = Real.exp (-1) ^ k := exp_neg_nat k
          unfold bt
          calc
            Real.exp (-(k : ℝ)) * ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
                = (n.choose k : ℝ) * (p ^ k * Real.exp (-(k : ℝ))) * (1 - p) ^ (n - k) := by ring
            _ = (n.choose k : ℝ) * (p ^ k * Real.exp (-1) ^ k) * (1 - p) ^ (n - k) := by
                  rw [he]
            _ = (n.choose k : ℝ) * (p * Real.exp (-1)) ^ k * (1 - p) ^ (n - k) := by
                  rw [← mul_pow]
            _ = (p * Real.exp (-1)) ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) := by ring
    _ = (p * Real.exp (-1) + (1 - p)) ^ n := h.symm
    _ = (1 - p + p * Real.exp (-1)) ^ n := by ring_nf

/-- `(1 - p + p e^{-1})^n ≤ e^{-np (1 - e^{-1})}` (using `1 - x ≤ e^{-x}`). -/
private lemma mgf_le (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p + p * Real.exp (-1)) ^ n ≤ Real.exp (-((n : ℝ) * p) * (1 - Real.exp (-1))) := by
  let e : ℝ := Real.exp (-1)
  have he0 : 0 < e := by simpa [e] using (Real.exp_pos (-1))
  have hbase0 : 0 ≤ 1 - p + p * e := by
    have : 0 ≤ p * e := mul_nonneg hp0 he0.le
    linarith
  have h1me : 0 ≤ 1 - e := by
    have he1 : e ≤ 1 := by
      dsimp [e]
      rw [← Real.exp_zero]
      exact (Real.exp_le_exp).2 (by norm_num)
    linarith
  have hb : 1 - p + p * e ≤ Real.exp (-(p * (1 - e))) := by
    have h := Real.add_one_le_exp (-(p * (1 - e)))
    calc
      1 - p + p * e = -(p * (1 - e)) + 1 := by
        dsimp [e]
        ring
      _ ≤ Real.exp (-(p * (1 - e))) := h
  have hpow : Real.exp (-(p * (1 - e))) ^ n = Real.exp (-((n : ℝ) * p * (1 - e))) := by
    rw [← Real.exp_nat_mul (-(p * (1 - e))) n]
    congr 1
    ring
  calc
    (1 - p + p * e) ^ n ≤ Real.exp (-(p * (1 - e))) ^ n := pow_le_pow_left₀ hbase0 hb n
    _ = Real.exp (-((n : ℝ) * p * (1 - e))) := hpow
    _ = Real.exp (-((n : ℝ) * p) * (1 - e)) := by congr 1; ring

/-- Chernoff domination: `P(K < m) ≤ e^{m-1} 𝔼[e^{-K}]`. -/
private lemma low_le_exp_mgf (n m : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hmn : m ≤ n) :
    (∑ k ∈ Finset.range m, bt n p k)
      ≤ Real.exp ((m : ℝ) - 1) * (∑ k ∈ Finset.range (n + 1), Real.exp (-(k : ℝ)) * bt n p k) := by
  let g : ℕ → ℝ := fun k => Real.exp ((m : ℝ) - 1 - (k : ℝ)) * bt n p k
  have hdom : ∀ k ∈ Finset.range m, bt n p k ≤ g k := by
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    have hksucc : k + 1 ≤ m := Nat.succ_le_of_lt hklt
    have hkreal : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hksucc
    have hnonneg_e : 0 ≤ (m : ℝ) - 1 - (k : ℝ) := by linarith
    have hone : 1 ≤ Real.exp ((m : ℝ) - 1 - (k : ℝ)) := Real.one_le_exp hnonneg_e
    have hbt0 : 0 ≤ bt n p k := bt_nonneg n p hp0 hp1 k
    unfold g
    exact le_mul_of_one_le_left hbt0 hone
  have h1 : (∑ k ∈ Finset.range m, bt n p k) ≤ (∑ k ∈ Finset.range m, g k) := Finset.sum_le_sum hdom
  have hsub : Finset.range m ⊆ Finset.range (n + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  have h2 : (∑ k ∈ Finset.range m, g k) ≤ (∑ k ∈ Finset.range (n + 1), g k) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro k hk hnot
    unfold g
    exact mul_nonneg (Real.exp_pos _).le (bt_nonneg n p hp0 hp1 k)
  have h3 : (∑ k ∈ Finset.range (n + 1), g k)
      = Real.exp ((m : ℝ) - 1) * (∑ k ∈ Finset.range (n + 1), Real.exp (-(k : ℝ)) * bt n p k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have h_exp : Real.exp ((m : ℝ) - 1 - (k : ℝ)) = Real.exp ((m : ℝ) - 1) * Real.exp (-(k : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
    unfold g
    calc
      Real.exp ((m : ℝ) - 1 - (k : ℝ)) * bt n p k
          = (Real.exp ((m : ℝ) - 1) * Real.exp (-(k : ℝ))) * bt n p k := by rw [h_exp]
      _ = Real.exp ((m : ℝ) - 1) * (Real.exp (-(k : ℝ)) * bt n p k) := by ring
  calc
    (∑ k ∈ Finset.range m, bt n p k) ≤ (∑ k ∈ Finset.range m, g k) := h1
    _ ≤ (∑ k ∈ Finset.range (n + 1), g k) := h2
    _ = Real.exp ((m : ℝ) - 1) * (∑ k ∈ Finset.range (n + 1), Real.exp (-(k : ℝ)) * bt n p k) := h3

/-- Numeric bound: `e^{-1} ≤ 2/5`. -/
private lemma exp_neg_one_le_two_fifths : Real.exp (-1) ≤ (2 / 5 : ℝ) := by
  have h := Real.exp_neg_one_lt_d9  -- exp (-1) < 0.3678794412
  norm_num at h ⊢
  linarith

/-- Numeric bound: `log 2 ≤ 11/10`. -/
private lemma log_two_le_eleven_tenths : Real.log 2 ≤ (11 / 10 : ℝ) := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

/-- Numeric bound: `e^{-log 4} = 1/4`. -/
private lemma exp_neg_log4 : Real.exp (-Real.log 4) = (1 / 4 : ℝ) := by
  have h4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num : 0 < (4 : ℝ))
  rw [Real.exp_neg, h4]
  norm_num

/-- Numeric bound: `e^{-11/5} ≤ 1/4`. -/
private lemma exp_neg_eleven_fifths_le_quarter : Real.exp (-(11 / 5 : ℝ)) ≤ (1 / 4 : ℝ) := by
  have hlog4 : Real.log 4 ≤ (11 / 5 : ℝ) := by
    rw [Real.log_four_eq]
    have h := log_two_le_eleven_tenths
    nlinarith
  have h : -(11 / 5 : ℝ) ≤ -Real.log 4 := by linarith
  have hm : Real.exp (-(11 / 5 : ℝ)) ≤ Real.exp (-Real.log 4) := (Real.exp_le_exp).2 h
  calc
    Real.exp (-(11 / 5 : ℝ)) ≤ Real.exp (-Real.log 4) := hm
    _ = 1 / 4 := exp_neg_log4

/-- Chernoff-type bound on the low tail: `P(K < m) ≤ 1/4` when `m ≤ np/2`, `np ≥ 12`. -/
private lemma bt_low_tail_le (n m : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hmn : m ≤ n)
    (hm : (m : ℝ) ≤ (n : ℝ) * p / 2) (hbig : (12 : ℝ) ≤ (n : ℝ) * p) :
    (∑ k ∈ Finset.range m, bt n p k) ≤ 1 / 4 := by
  let e : ℝ := Real.exp (-1)
  let μ : ℝ := (n : ℝ) * p
  have hS1 : (∑ k ∈ Finset.range m, bt n p k)
      ≤ Real.exp ((m : ℝ) - 1) * ((1 - p + p * Real.exp (-1)) ^ n) := by
    calc
      (∑ k ∈ Finset.range m, bt n p k)
          ≤ Real.exp ((m : ℝ) - 1) * (∑ k ∈ Finset.range (n + 1), Real.exp (-(k : ℝ)) * bt n p k) :=
            low_le_exp_mgf n m p hp0 hp1 hmn
      _ = Real.exp ((m : ℝ) - 1) * (1 - p + p * Real.exp (-1)) ^ n := by
            rw [mgf_sum_eq]
  have hS2 : Real.exp ((m : ℝ) - 1) * (1 - p + p * Real.exp (-1)) ^ n
      ≤ Real.exp ((m : ℝ) - 1) * Real.exp (-(μ * (1 - e))) := by
    have hmgf := mgf_le n p hp0 hp1
    have hcon : Real.exp (-(μ * (1 - e))) = Real.exp (-((n : ℝ) * p) * (1 - Real.exp (-1))) := by
      dsimp [μ, e]
      congr 1
      ring
    have hle : (1 - p + p * Real.exp (-1)) ^ n ≤ Real.exp (-(μ * (1 - e))) := by
      rw [hcon]
      exact hmgf
    exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
  have hS3 : Real.exp ((m : ℝ) - 1) * Real.exp (-(μ * (1 - e)))
      = Real.exp ((m : ℝ) - 1 - μ * (1 - e)) := by
    rw [← Real.exp_add]
    congr 1
  have hE : (m : ℝ) - 1 - μ * (1 - e) ≤ -(11 / 5 : ℝ) := by
    have he_le : e ≤ (2 / 5 : ℝ) := by
      dsimp [e]
      exact exp_neg_one_le_two_fifths
    have ha : (1 / 10 : ℝ) ≤ 1 / 2 - e := by linarith
    have ha0 : 0 ≤ 1 / 2 - e := by linarith
    have hμ12 : (12 : ℝ) ≤ μ := by
      dsimp [μ]
      exact hbig
    have hm1 : (m : ℝ) - 1 ≤ μ / 2 - 1 := by
      dsimp [μ]
      linarith
    have h12a : (12 : ℝ) * (1 / 10) ≤ (12 : ℝ) * (1 / 2 - e) := by
      exact mul_le_mul_of_nonneg_left ha (by norm_num : 0 ≤ (12 : ℝ))
    have hμa : (12 : ℝ) * (1 / 2 - e) ≤ μ * (1 / 2 - e) := by
      exact mul_le_mul_of_nonneg_right hμ12 ha0
    have hμa' : (6 / 5 : ℝ) ≤ μ * (1 / 2 - e) := by
      calc
        (6 / 5 : ℝ) = (12 : ℝ) * (1 / 10) := by norm_num
        _ ≤ (12 : ℝ) * (1 / 2 - e) := h12a
        _ ≤ μ * (1 / 2 - e) := hμa
    calc
      (m : ℝ) - 1 - μ * (1 - e) ≤ (μ / 2 - 1) - μ * (1 - e) := by
        exact sub_le_sub_right hm1 (μ * (1 - e))
      _ = -1 - μ * (1 / 2 - e) := by ring
      _ ≤ -1 - (6 / 5 : ℝ) := by
        exact sub_le_sub_left hμa' (-1 : ℝ)
      _ ≤ -(11 / 5 : ℝ) := by norm_num
  calc
    (∑ k ∈ Finset.range m, bt n p k)
        ≤ Real.exp ((m : ℝ) - 1) * (1 - p + p * Real.exp (-1)) ^ n := hS1
    _ ≤ Real.exp ((m : ℝ) - 1) * Real.exp (-(μ * (1 - e))) := hS2
    _ = Real.exp ((m : ℝ) - 1 - μ * (1 - e)) := hS3
    _ ≤ Real.exp (-(11 / 5 : ℝ)) := (Real.exp_le_exp).2 hE
    _ ≤ 1 / 4 := exp_neg_eleven_fifths_le_quarter

/--
Chernoff-type lower bound: if `m ≤ np/2` and `np ≥ 12` then `P(Bin(n,p) ≥ m) ≥ 3/4`.

Sketch: `P(K < m) ≤ P(K ≤ np/2) ≤ exp(-np/8) ≤ exp(-12/8) < 1/4`, using the
multiplicative Chernoff bound `P(K ≤ (1-δ)μ) ≤ exp(-δ²μ/2)` for `δ = 1/2`
(prove it from Markov's inequality with the moment generating function
`E[e^{-tK}] = (1 - p + p·e^{-t})^n ≤ exp(-p n (1 - e^{-t}))` and `t = 1/2`,
using `1 - x ≤ exp(-x)` and `1 - e^{-1/2} ≥ 1/3`, say).
-/
lemma binom_tail_lower (n m : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hmn : m ≤ n)
    (hm : (m : ℝ) ≤ (n : ℝ) * p / 2) (hbig : (12 : ℝ) ≤ (n : ℝ) * p) :
    (3 / 4 : ℝ) ≤ binomTail n m p := by
  have hS : (∑ k ∈ Finset.range m, bt n p k) ≤ 1 / 4 := bt_low_tail_le n m p hp0 hp1 hmn hm hbig
  have hEq : binomTail n m p = 1 - (∑ k ∈ Finset.range m, bt n p k) :=
    binomTail_eq_one_sub_low n m p hmn
  rw [hEq]
  linarith

end FET
end Submission
