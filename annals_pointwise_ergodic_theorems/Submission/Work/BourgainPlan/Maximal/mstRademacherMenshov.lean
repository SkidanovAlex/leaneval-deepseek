import Mathlib

/-!
# MST's numerical maximal inequality (Rademacher–Menshov, eq. (2.21))

Mirek–Stein–Trojan, *ℓ^p bounds for discrete Radon transforms* (arXiv:1512.07518), Lemma 6
(eq. `eq:21`), in the form in which they use it: the **supremum of a sequence is dominated by the
dyadic block square functions of its increments**, with a constant uniform in the length.

> For every `s`, every sequence `(a_j)_{0 ≤ j ≤ 2^s}` in a seminormed group and every `j, j₀ ≤ 2^s`,
> `‖a j − a j₀‖ ≤ 2 · Σ_{i=0}^{s} ( Σ_{m<2^{s−i}} ‖a ((m+1)·2^i) − a (m·2^i)‖² )^{1/2}`.

The summand at level `i` is the `ℓ²`-square function of the **blocks of length `2^i`** of the
sequence: `a ((m+1)2^i) − a (m 2^i) = Σ_{k ∈ [m2^i, (m+1)2^i)} (a_{k+1} − a_k)`.

Two features make this the tool of choice for maximal estimates (and are exactly why it is used in
the modern (Ionescu–Wainger) route):

* the number of **levels** is `s = log₂ (length)`, i.e. the *logarithm* of the number of scales;
* the level-`i` blocks are the *dyadic* blocks of the **index**, so in the applications the level-`i`
  square functions are the projections onto the dyadic blocks of the exponent — which is what the
  Ionescu–Wainger type multiplier theorems bound (Kosz–Mirek–Słomian–Zhang, Definition 5.1(2), make
  this inequality an *axiom* of their `Rademacher–Menshov seminorm` framework; MST use it in the
  proof of their Theorem 2 with `a_n` the `ℓ²(ℤ^d)`-valued sequence `n ↦ 𝓕^{-1}(ν^s_{2^n} f̂)`).

Consequently, when the level-`i` square functions carry a decay in the *level parameter* of the
original problem (MST: the number of prime factors of the denominator; Bourgain §7.3: the count of
sub-sums), the sum over the `≤ log₂ (number of scales)` levels produces exactly a `log log` loss —
the loss of Bourgain's (7.35) and of the target `WindowWeakType`.

The constant here is `2` (MST's `√2` comes from an even/odd splitting); any absolute constant
serves in the applications and the level structure is preserved verbatim.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The dyadic **block square function** of a sequence at level `i`:
`(Σ_{m < 2^{s-i}} ‖a ((m+1)·2^i) − a (m·2^i)‖²)^{1/2}`; the `m`-th summand is the increment of `a`
over the index block `[m·2^i, (m+1)·2^i)`. -/
def rmLevel (s i : ℕ) (a : ℕ → E) : ℝ :=
  Real.sqrt (∑ m ∈ Finset.range (2 ^ (s - i)), ‖a ((m + 1) * 2 ^ i) - a (m * 2 ^ i)‖ ^ 2)

lemma rmLevel_nonneg (s i : ℕ) (a : ℕ → E) : 0 ≤ rmLevel s i a := Real.sqrt_nonneg _

/-- `rmL i j = 2^i · ⌊j / 2^i⌋`, the largest multiple of `2^i` below `j`. -/
def rmL (i j : ℕ) : ℕ := j / 2 ^ i * 2 ^ i

lemma rmL_le (i j : ℕ) : rmL i j ≤ j := Nat.div_mul_le_self _ _

lemma rmL_zero (j : ℕ) : rmL 0 j = j := by simp [rmL]

/-- `rmL i j = rmL (i+1) j + b·2^i` where `b = (j / 2^i) % 2 ∈ {0,1}` is the `i`-th bit of `j`. -/
lemma rmL_step (i j : ℕ) :
    rmL i j = rmL (i + 1) j + (j / 2 ^ i % 2) * 2 ^ i := by
  have h1 : j / 2 ^ (i + 1) = j / 2 ^ i / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have key : j / 2 ^ i * 2 ^ i
      = (j / 2 ^ (i + 1)) * 2 ^ (i + 1) + (j / 2 ^ i % 2) * 2 ^ i := by
    rw [h1]
    set n := j / 2 ^ i with hn
    have h2 : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
    calc n * 2 ^ i = (2 * (n / 2) + n % 2) * 2 ^ i := by
          conv_lhs => rw [h2]
      _ = 2 * (n / 2) * 2 ^ i + (n % 2) * 2 ^ i := by ring
      _ = n / 2 * 2 ^ (i + 1) + (n % 2) * 2 ^ i := by rw [pow_succ]; ring
  unfold rmL
  exact key

/-- The multiple of `2^i` in the chain step is `m·2^i` with `m = 2⌊j/2^{i+1}⌋`. -/
lemma rmL_succ_eq (i j : ℕ) : rmL (i + 1) j = (2 * (j / 2 ^ (i + 1))) * 2 ^ i := by
  unfold rmL
  rw [pow_succ]
  ring

/-- The top level: `rmL s j` is `0` or `2^s` when `j ≤ 2^s`. -/
lemma rmL_top (s j : ℕ) (hj : j ≤ 2 ^ s) : rmL s j = 0 ∨ rmL s j = 2 ^ s := by
  have hpos : 0 < 2 ^ s := by positivity
  have hle : j / 2 ^ s ≤ 2 ^ s / 2 ^ s := Nat.div_le_div_right hj
  rw [Nat.div_self hpos] at hle
  interval_cases hd : j / 2 ^ s
  · left; unfold rmL; rw [hd]; simp
  · right; unfold rmL; rw [hd]; ring

/-- **The level-`i` chain term is dominated by the level-`i` block square function.** -/
lemma rmL_diff_le (s i : ℕ) (a : ℕ → E) {j : ℕ} (hi : i < s) (hj : j ≤ 2 ^ s) :
    ‖a (rmL i j) - a (rmL (i + 1) j)‖ ≤ rmLevel s i a := by
  rcases Nat.eq_zero_or_pos (j / 2 ^ i % 2) with hb | hb
  · have hz : rmL i j = rmL (i + 1) j := by rw [rmL_step i j, hb, zero_mul, add_zero]
    rw [hz, sub_self, norm_zero]
    exact rmLevel_nonneg _ _ _
  · have hb1 : j / 2 ^ i % 2 = 1 := by omega
    set m : ℕ := 2 * (j / 2 ^ (i + 1)) with hm
    have hstep : rmL i j = rmL (i + 1) j + 2 ^ i := by
      rw [rmL_step i j, hb1, one_mul]
    have hL : rmL (i + 1) j = m * 2 ^ i := rmL_succ_eq i j
    have hindex : rmL i j = (m + 1) * 2 ^ i := by
      rw [hstep, hL]; ring
    have hmem : m ∈ Finset.range (2 ^ (s - i)) := by
      rw [Finset.mem_range]
      have h2 : (m + 1) * 2 ^ i ≤ 2 ^ s := by
        rw [← hindex]; exact le_trans (rmL_le i j) hj
      have h3 : 2 ^ s = 2 ^ (s - i) * 2 ^ i := by
        rw [mul_comm, ← pow_add]; congr 1; omega
      rw [h3] at h2
      have := Nat.le_of_mul_le_mul_right h2 (by positivity : 0 < 2 ^ i)
      omega
    have hsummand : ‖a ((m + 1) * 2 ^ i) - a (m * 2 ^ i)‖ ^ 2
        ≤ ∑ m' ∈ Finset.range (2 ^ (s - i)), ‖a ((m' + 1) * 2 ^ i) - a (m' * 2 ^ i)‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun m' => ‖a ((m' + 1) * 2 ^ i) - a (m' * 2 ^ i)‖ ^ 2)
        (fun m' _ => by positivity) hmem
    rw [hindex, hL]
    exact Real.le_sqrt_of_sq_le hsummand

/-- The top-level term: the difference of the two rounded indices is at most the level-`s`
block square function (which is the single increment `‖a (2^s) − a 0‖`). -/
lemma rmL_top_le (s : ℕ) (a : ℕ → E) {j j₀ : ℕ} (hj : j ≤ 2 ^ s) (hj₀ : j₀ ≤ 2 ^ s) :
    ‖a (rmL s j) - a (rmL s j₀)‖ ≤ rmLevel s s a := by
  have htop : rmLevel s s a = ‖a (2 ^ s) - a 0‖ := by
    rw [rmLevel, Nat.sub_self, pow_zero, Finset.range_one, Finset.sum_singleton]
    simp only [zero_add, one_mul, zero_mul]
    rw [Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (norm_nonneg (a (2 ^ s) - a 0))
  have hj2 : rmL s j = 0 ∨ rmL s j = 2 ^ s := rmL_top s j hj
  have hj2' : rmL s j₀ = 0 ∨ rmL s j₀ = 2 ^ s := rmL_top s j₀ hj₀
  rw [htop]
  rcases hj2 with h | h <;> rcases hj2' with h' | h'
  · rw [h, h', sub_self, norm_zero]
    exact norm_nonneg (a (2 ^ s) - a 0)
  · rw [h, h', norm_sub_rev]
  · rw [h, h']
  · rw [h, h', sub_self, norm_zero]
    exact norm_nonneg (a (2 ^ s) - a 0)

/-- **The chain inequality**: from `j` down to `rmL s j`. -/
lemma rmL_chain_le (s : ℕ) (a : ℕ → E) {j : ℕ} (hj : j ≤ 2 ^ s) :
    ‖a j - a (rmL s j)‖ ≤ ∑ i ∈ Finset.range s, rmLevel s i a := by
  have htel : ∑ i ∈ Finset.range s, (a (rmL i j) - a (rmL (i + 1) j))
      = a j - a (rmL s j) := by
    rw [Finset.sum_range_sub' (f := fun i => a (rmL i j)) s, rmL_zero]
  rw [← htel]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum (fun i hi => ?_)
  exact rmL_diff_le s i a (Finset.mem_range.mp hi) hj

/-- **MST Lemma 6 (eq. (2.21)) in a seminormed group.**  For every sequence `a : ℕ → E` and all
`j, j₀ ≤ 2^s`,

`‖a j − a j₀‖ ≤ 2 · Σ_{i=0}^{s} (Σ_{m < 2^{s-i}} ‖a ((m+1)·2^i) − a (m·2^i)‖²)^{1/2}`.

The number of levels is `s + 1 = log₂(length) + 1`, and each level is the `ℓ²`-square function of
the *dyadic blocks of the index*. -/
theorem rm_le_sum_levels (s : ℕ) (a : ℕ → E) {j j₀ : ℕ} (hj : j ≤ 2 ^ s) (hj₀ : j₀ ≤ 2 ^ s) :
    ‖a j - a j₀‖ ≤ 2 * ∑ i ∈ Finset.range (s + 1), rmLevel s i a := by
  have key : a j - a j₀
      = (a j - a (rmL s j)) + (a (rmL s j) - a (rmL s j₀)) + (a (rmL s j₀) - a j₀) := by abel
  have hsum_succ : ∑ i ∈ Finset.range (s + 1), rmLevel s i a
      = (∑ i ∈ Finset.range s, rmLevel s i a) + rmLevel s s a := Finset.sum_range_succ _ _
  have hsplit : (∑ i ∈ Finset.range s, rmLevel s i a) ≤ ∑ i ∈ Finset.range (s + 1), rmLevel s i a := by
    rw [hsum_succ]; exact le_add_of_nonneg_right (rmLevel_nonneg _ _ _)
  rw [key]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  have h1 := rmL_chain_le s a hj
  have h2 := rmL_top_le s a hj hj₀
  have h3 := rmL_chain_le s a hj₀
  have h3' : ‖a (rmL s j₀) - a j₀‖ ≤ ∑ i ∈ Finset.range s, rmLevel s i a := by
    rw [← norm_neg]; simpa using h3
  have hS : (0:ℝ) ≤ ∑ i ∈ Finset.range s, rmLevel s i a :=
    Finset.sum_nonneg (fun i _ => rmLevel_nonneg _ _ _)
  calc ‖a j - a (rmL s j)‖ + ‖a (rmL s j) - a (rmL s j₀)‖ + ‖a (rmL s j₀) - a j₀‖
      ≤ (∑ i ∈ Finset.range s, rmLevel s i a) + rmLevel s s a
          + (∑ i ∈ Finset.range s, rmLevel s i a) := by
        exact add_le_add (add_le_add h1 h2) h3'
    _ ≤ 2 * ∑ i ∈ Finset.range (s + 1), rmLevel s i a := by
        rw [hsum_succ]
        linarith

/-- **The Rademacher–Menshov reduction of a window `sup`.**  For a sequence `a` and an index window
`[n₀, K]`, the deviation from the base value `a n₀` is dominated by the dyadic block square
functions of the *shifted* sequence, at the `≈ log₂ (K - n₀)` levels:

`⨆_{n₀ ≤ k ≤ K} ‖a k − a n₀‖ ≤ 2 · Σ_{i = 0}^{⌈log₂ (K−n₀+1)⌉} (Σ_m ‖a (n₀+(m+1)2^i) − a (n₀+m2^i)‖²)^{1/2}`.

This is the step that converts a *window maximal* estimate into an estimate for the dyadic block
square functions of the averages — with the loss being the **number of levels**, i.e. the logarithm
of the number of scales of the window.  For the windows `(N₀, N₀^{1+ε}]` of `WindowWeakType` the
number of scales is `≍ log N₀`, hence the number of levels is `≍ log log N₀`: this is where the
`log log N₀` of Bourgain's (7.35) comes from. -/
theorem rm_iSup_window_le (n₀ K : ℕ) (a : ℕ → E) :
    (⨆ k ∈ Finset.Icc n₀ K, ‖a k - a n₀‖ₑ) ≤
      ENNReal.ofReal (2 * ∑ i ∈ Finset.range (Nat.clog 2 (K - n₀ + 1) + 1),
        rmLevel (Nat.clog 2 (K - n₀ + 1)) i (fun r => a (n₀ + r))) := by
  have hK : K - n₀ ≤ 2 ^ Nat.clog 2 (K - n₀ + 1) := by
    have h := Nat.le_pow_clog (b := 2) (by norm_num) (K - n₀ + 1)
    omega
  refine iSup₂_le (fun k hk => ?_)
  have hk' : k ≤ K := (Finset.mem_Icc.mp hk).2
  have hk'' : n₀ ≤ k := (Finset.mem_Icc.mp hk).1
  have hjk : k - n₀ ≤ 2 ^ Nat.clog 2 (K - n₀ + 1) := le_trans (by omega) hK
  have h := rm_le_sum_levels (Nat.clog 2 (K - n₀ + 1)) (fun r => a (n₀ + r)) hjk
    (by positivity : (0:ℕ) ≤ 2 ^ Nat.clog 2 (K - n₀ + 1))
  rw [show n₀ + (k - n₀) = k from by omega, show n₀ + 0 = n₀ from rfl] at h
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h


end

end Work.BourgainPlan.Maximal
