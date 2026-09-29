import Mathlib
import Submission.Work.SynFFT.defs
import Submission.Work.SynFFT.yMulAlg
import Submission.Work.SynFFT.bitrevFacts
import Submission.Work.SynFFT.dftHalfArith

/-!
# `dft1Math`: one radix-two Cooley–Tukey level of the synthetic FFT

This file proves `Work.SynFFT.dft1Math`, the mathematical core of the one-dimensional
synthetic transform over `R = ℂ[y]/(y^r+1)` (paper Lemma 3.2 and the ordering part of
Proposition 3.3).

Setting: `t = 2^k` (`k ≥ 1`) with `t ∣ 2r`, `sgn = ±1`, `a : Arr r = ℕ → Fin r → ℂ`.

* `dftN r t sgn a j = (1/t) Σ_{k<t} y^{sgn·(2r/t)·j·k} · a_k` is the length-`t` synthetic DFT.
* `lvlN r t sgn` is one radix-two butterfly stage of block size `t`; `levels r sgn t k` is the
  composition of the stages of sizes `t, t/2, …, t/2^(k-1)`.

The two assertions are

1. `levels r sgn t (log₂ t) a p = dftN r t sgn a (bitrev (log₂ t) p)` — the iterative radix-two
   algorithm computes the DFT in bit-reversed output order;
2. the Cooley–Tukey recursion `dftN r t sgn a (2l) = dftN r (t/2) sgn (a₊) l` and
   `dftN r t sgn a (2l+1) = dftN r (t/2) sgn (a₋) l` with `a₊ k = (a_k + a_{k+t/2})/2` and
   `a₋ k = y^{sgn·(2r/t)·k}(a_k - a_{k+t/2})/2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH
open scoped BigOperators

/-! ## Elementary consequences of the `ℤ`-action laws of `yMul` -/

section YMulLemmas

variable {r : ℕ}

/-- `yMul r` is trivial at exponents that are multiples of `2r`. -/
lemma yMul_two_r_mul (hr : 0 < r) (n : ℤ) (a : Fin r → ℂ) :
    yMul r (2 * (r : ℤ) * n) a = a := by
  obtain ⟨-, hzero, -, -, hper, -, -⟩ := yMulAlg r hr
  have h := hper 0 n a
  rw [zero_add] at h
  rw [h, hzero]

/-- `yMul r` is `-1` at odd multiples of `r`. -/
lemma yMul_r_odd (hr : 0 < r) (n : ℤ) (a : Fin r → ℂ) :
    yMul r ((r : ℤ) * (2 * n + 1)) a = -a := by
  obtain ⟨-, -, -, -, hper, -, hhalf⟩ := yMulAlg r hr
  have h : (r : ℤ) * (2 * n + 1) = (r : ℤ) + 2 * (r : ℤ) * n := by ring
  rw [h, hper, hhalf]

/-- The twiddle `y^{sgn·(2l+1)r}` of the odd part of one Cooley–Tukey level is `-1`. -/
lemma yMul_sgn_odd (hr : 0 < r) {sgn : ℤ} (hsgn : sgn = 1 ∨ sgn = -1) (l : ℕ)
    (a : Fin r → ℂ) : yMul r (sgn * (((2 * l + 1) * r : ℕ) : ℤ)) a = -a := by
  rcases hsgn with h | h
  · rw [h, one_mul]
    have hc : (((2 * l + 1) * r : ℕ) : ℤ) = (r : ℤ) * (2 * (l : ℤ) + 1) := by
      push_cast; ring
    rw [hc]; exact yMul_r_odd hr (l : ℤ) a
  · rw [h, neg_one_mul]
    have hc : -(((2 * l + 1) * r : ℕ) : ℤ) = (r : ℤ) * (2 * (-(l : ℤ) - 1) + 1) := by
      push_cast; ring
    rw [hc]; exact yMul_r_odd hr (-(l : ℤ) - 1) a

/-- The twiddle `y^{sgn·2lr}` of the even part of one Cooley–Tukey level is `1`. -/
lemma yMul_sgn_two_l_r (hr : 0 < r) (sgn : ℤ) (l : ℕ) (a : Fin r → ℂ) :
    yMul r (sgn * ((2 * l * r : ℕ) : ℤ)) a = a := by
  have hc : sgn * ((2 * l * r : ℕ) : ℤ) = 2 * (r : ℤ) * (sgn * (l : ℤ)) := by
    push_cast; ring
  rw [hc]; exact yMul_two_r_mul hr (sgn * (l : ℤ)) a

/-- `yMul r e` is `-1` on negated vectors. -/
lemma yMul_neg (hr : 0 < r) (e : ℤ) (v : Fin r → ℂ) : yMul r e (-v) = - yMul r e v := by
  obtain ⟨-, -, -, hsmul, -, -, -⟩ := yMulAlg r hr
  have h := hsmul e (-1) v
  rw [show (-1 : ℂ) • v = -v by simp] at h
  simpa using h

/-- Additivity of `yMul` in the vector, evaluated pointwise. -/
lemma yMul_add_apply (hr : 0 < r) (e : ℤ) (x y : Fin r → ℂ) (c : Fin r) :
    yMul r e x c + yMul r e y c = yMul r e (x + y) c := by
  obtain ⟨-, -, hadd, -, -, -, -⟩ := yMulAlg r hr
  rw [← Pi.add_apply, ← hadd]

/-- Negation of `yMul`, evaluated pointwise. -/
lemma yMul_neg_apply (hr : 0 < r) (e : ℤ) (v : Fin r → ℂ) (c : Fin r) :
    yMul r e (-v) c = - yMul r e v c := by
  rw [yMul_neg hr e v, Pi.neg_apply]

/-- The neutral form `v = 2 • (v/2)` pushed inside `yMul`. -/
lemma yMul_half (hr : 0 < r) (e : ℤ) (v : Fin r → ℂ) (c : Fin r) :
    yMul r e v c = 2 * (yMul r e (v / 2) c) := by
  obtain ⟨-, -, -, hsmul, -, -, -⟩ := yMulAlg r hr
  have hv : v = (2 : ℂ) • (v / 2) := by
    funext k
    show v k = 2 * (v k / 2)
    ring
  conv_lhs => rw [hv, hsmul]
  exact smul_eq_mul 2 _

end YMulLemmas

/-! ## The two halves of one butterfly stage -/

section LevelLemmas

variable {r : ℕ}

/-- The lower half of a butterfly stage is the "sum" array. -/
lemma lvlN_apply_left (sgn : ℤ) (t : ℕ) (a : Arr r) (u : ℕ) (hu : u < t / 2) :
    lvlN r t sgn a u = fun c => (a u c + a (u + t / 2) c) / 2 := by
  funext c
  have hut : u < t := by omega
  simp only [lvlN, Nat.mod_eq_of_lt hut, if_pos hu]

/-- The upper half of a butterfly stage is the "difference" array with the twiddle. -/
lemma lvlN_apply_right (sgn : ℤ) (t : ℕ) (a : Arr r) (u : ℕ) (hu : u < t / 2) :
    lvlN r t sgn a (u + t / 2) = fun c =>
      yMul r (sgn * (((2 * r / t) * u : ℕ) : ℤ))
        (fun c' => (a u c' - a (u + t / 2) c') / 2) c := by
  funext c
  have hut : u + t / 2 < t := by omega
  have hlt : ¬ (u + t / 2 < t / 2) := by omega
  simp only [lvlN, Nat.mod_eq_of_lt hut, if_neg hlt, show u + t / 2 - t / 2 = u by omega]

/-- `lvlN` is insensitive to shifting the array by a multiple of the block size. -/
lemma lvlN_shift (m S : ℕ) (sgn : ℤ) (a : Arr r) (hS : m ∣ S) :
    lvlN r m sgn (fun p => a (p + S)) = fun q => lvlN r m sgn a (q + S) := by
  funext q c
  simp only [lvlN]
  have hmod : (q + S) % m = q % m := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hS, Nat.add_zero, Nat.mod_mod]
  by_cases hc : q % m < m / 2
  · simp only [hmod, if_pos hc]
    rw [show q + m / 2 + S = q + S + m / 2 by omega]
  · simp only [hmod, if_neg hc]
    have hq : m / 2 ≤ q := le_trans (Nat.le_of_not_lt hc) (Nat.mod_le q m)
    rw [show q - m / 2 + S = q + S - m / 2 by omega]

/-- The levels of the radix-two recursion commute with a shift of the array by a multiple of
every stage size: `m/2^j ∣ S` for all stages `j < k`. -/
lemma levels_shift (sgn : ℤ) :
    ∀ (k m S : ℕ) (a : Arr r), (∀ j < k, m / 2 ^ j ∣ S) →
      levels r sgn m k (fun p => a (p + S)) = fun q => levels r sgn m k a (q + S) := by
  intro k
  induction k with
  | zero => intro m S a _; rfl
  | succ k ih =>
      intro m S a h
      have hsh := lvlN_shift m S sgn a (by simpa using h 0 (Nat.succ_pos k))
      have h2 : ∀ j < k, m / 2 / 2 ^ j ∣ S := by
        intro j hj
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
        exact h (j + 1) (by omega)
      change levels r sgn (m / 2) k (lvlN r m sgn (fun p => a (p + S))) =
        fun q => levels r sgn (m / 2) k (lvlN r m sgn a) (q + S)
      rw [hsh]
      exact ih (m / 2) S (lvlN r m sgn a) h2

/-- Pointwise form of `levels_shift`. -/
lemma levels_shift_apply (sgn : ℤ) (k m S : ℕ) (a : Arr r)
    (hS : ∀ j < k, m / 2 ^ j ∣ S) (q : ℕ) :
    levels r sgn m k a (q + S) = levels r sgn m k (fun p => a (p + S)) q :=
  (congr_fun (levels_shift (r := r) sgn k m S a hS) q).symm

/-- `lvlN` only depends on the array below the block size. -/
lemma lvlN_congr (m : ℕ) (sgn : ℤ) {a b : Arr r} (h : ∀ q < m, a q = b q) :
    ∀ p < m, lvlN r m sgn a p = lvlN r m sgn b p := by
  intro p hp
  funext c
  simp only [lvlN]
  rw [Nat.mod_eq_of_lt hp]
  by_cases hc : p < m / 2
  · simp only [if_pos hc, h p hp, h (p + m / 2) (by omega)]
  · simp only [if_neg hc, h (p - m / 2) (by omega), h p hp]

/-- `2^(k+1)/2 = 2^k`. -/
lemma two_pow_succ_div_two (k : ℕ) : 2 ^ (k + 1) / 2 = 2 ^ k := by
  rw [pow_succ]
  simp

/-- `levels` only depends on the array below the current block size `m` (a power of two). -/
lemma levels_congr (sgn : ℤ) (k : ℕ) :
    ∀ (m : ℕ), m = 2 ^ k → ∀ {a b : Arr r}, (∀ q < m, a q = b q) → ∀ p < m,
      levels r sgn m k a p = levels r sgn m k b p := by
  induction k with
  | zero =>
      intro m hm a b h p hp
      exact h p (by omega)
  | succ k ih =>
      intro m hm a b h p hp
      have hm2 : m / 2 = 2 ^ k := by rw [hm, two_pow_succ_div_two]
      have h2 : ∀ q < m, lvlN r m sgn a q = lvlN r m sgn b q := fun q hq => lvlN_congr m sgn h q hq
      have hdvd : ∀ j < k, m / 2 / 2 ^ j ∣ m / 2 := by
        intro j hj
        rw [hm2, Nat.pow_div (by omega : j ≤ k) (by norm_num : 0 < 2)]
        exact Nat.pow_dvd_pow 2 (by omega : k - j ≤ k)
      by_cases hp2 : p < m / 2
      · exact ih (m / 2) hm2 (fun q hq => h2 q (by omega)) p hp2
      · have hp' : p - m / 2 < m / 2 := by omega
        have hA := levels_shift_apply (r := r) sgn k (m / 2) (m / 2) (lvlN r m sgn a) hdvd (p - m / 2)
        have hB := levels_shift_apply (r := r) sgn k (m / 2) (m / 2) (lvlN r m sgn b) hdvd (p - m / 2)
        show levels r sgn (m / 2) k (lvlN r m sgn a) p = levels r sgn (m / 2) k (lvlN r m sgn b) p
        rw [show p = p - m / 2 + m / 2 by omega, hA, hB]
        exact ih (m / 2) hm2 (fun q hq => h2 (q + m / 2) (by omega)) (p - m / 2) hp'

end LevelLemmas

/-! ## The Cooley–Tukey recursion (one radix-two level of the synthetic DFT) -/

/-- The Cooley–Tukey recursion of the synthetic DFT over `ℂ[y]/(y^r+1)`: for a length
`t = 2^k` (`k ≥ 1`) dividing `2r`, the length-`t` transform of `a` at the even outputs
`2l` is the length-`t/2` transform of `(a_k + a_{k+t/2})/2`, and at the odd outputs
`2l+1` it is the length-`t/2` transform of `y^{sgn·(2r/t)·k}(a_k - a_{k+t/2})/2`. -/
theorem dftParts (r t : ℕ) (sgn : ℤ) (hr : 0 < r) (hsgn : sgn = 1 ∨ sgn = -1)
    (ht : ∃ k : ℕ, 1 ≤ k ∧ t = 2 ^ k) (htr : t ∣ 2 * r) :
    ∀ (a : Arr r) (l : ℕ), l < t / 2 →
      dftN r t sgn a (2 * l) =
        dftN r (t / 2) sgn (fun k c => (a k c + a (k + t / 2) c) / 2) l ∧
      dftN r t sgn a (2 * l + 1) =
        dftN r (t / 2) sgn (fun k c =>
          yMul r (sgn * (((2 * r / t) * k : ℕ) : ℤ))
            (fun c' => (a k c' - a (k + t / 2) c') / 2) c) l := by
  obtain ⟨hcomp, hzero, hadd, hsmul, hper, htwo, hhy⟩ := yMulAlg r hr
  obtain ⟨h2t, hs0, h2s, hsd, hdiv, hmul, hm0⟩ := dftHalfArith r t hr ht htr
  have hs : t = t / 2 + t / 2 := by omega
  have hsc : ((t / 2 : ℕ) : ℂ) ≠ 0 := by
    have h : (t / 2 : ℕ) ≠ 0 := by omega
    exact_mod_cast h
  have htcast : (t : ℂ) = 2 * ((t / 2 : ℕ) : ℂ) := by
    rw [← Nat.cast_two, ← Nat.cast_mul, h2s]
  have hhalf : (1 / (t : ℂ)) * 2 = 1 / ((t / 2 : ℕ) : ℂ) := by
    rw [htcast]
    field_simp
  intro a l hl
  refine ⟨?_, ?_⟩
  · funext c
    simp only [dftN]
    rw [congrArg Finset.range hs, Finset.sum_range_add]
    rw [hdiv]
    rw [show (2 : ℕ) * (2 * r / t) * l = (2 * r / t) * (2 * l) by ring]
    have hterm : ∀ i : ℕ, i < t / 2 →
        yMul r (sgn * (((2 * r / t * (2 * l)) * (t / 2 + i) : ℕ) : ℤ)) (a (t / 2 + i)) c
          = yMul r (sgn * (((2 * r / t * (2 * l)) * i : ℕ) : ℤ)) (a (i + t / 2)) c := by
      intro i hi
      rw [show t / 2 + i = i + t / 2 by omega]
      have hnat : (2 * r / t * (2 * l)) * (i + t / 2) = (2 * r / t * (2 * l)) * i + 2 * l * r := by
        rw [mul_add, show 2 * r / t * (2 * l) * (t / 2) = 2 * l * r by
          rw [show 2 * r / t * (2 * l) * (t / 2) = 2 * l * ((2 * r / t) * (t / 2)) by ring,
            hmul]]
      calc yMul r (sgn * (((2 * r / t * (2 * l)) * (i + t / 2) : ℕ) : ℤ)) (a (i + t / 2)) c
          = yMul r (sgn * ((((2 * r / t * (2 * l)) * i + 2 * l * r : ℕ)) : ℤ)) (a (i + t / 2)) c := by
            rw [hnat]
        _ = yMul r (sgn * (((2 * r / t * (2 * l)) * i : ℕ) : ℤ) + sgn * ((2 * l * r : ℕ) : ℤ))
              (a (i + t / 2)) c := by rw [Nat.cast_add, mul_add]
        _ = yMul r (sgn * (((2 * r / t * (2 * l)) * i : ℕ) : ℤ))
              (yMul r (sgn * ((2 * l * r : ℕ) : ℤ)) (a (i + t / 2))) c := by rw [hcomp]
        _ = yMul r (sgn * (((2 * r / t * (2 * l)) * i : ℕ) : ℤ)) (a (i + t / 2)) c := by
              rw [yMul_sgn_two_l_r hr sgn l]
    rw [Finset.sum_congr rfl (fun i hi => hterm i (Finset.mem_range.mp hi))]
    rw [← Finset.sum_add_distrib]
    have hkey : ∀ i : ℕ, i < t / 2 →
        yMul r (sgn * (((2 * r / t * (2 * l)) * i : ℕ) : ℤ)) (a i) c
          + yMul r (sgn * (((2 * r / t * (2 * l)) * i : ℕ) : ℤ)) (a (i + t / 2)) c
          = 2 * (yMul r (sgn * (((2 * r / t * (2 * l)) * i : ℕ) : ℤ))
              ((a i + a (i + t / 2)) / 2) c) := by
      intro i hi
      rw [yMul_add_apply hr, yMul_half hr]
    rw [Finset.sum_congr rfl (fun i hi => hkey i (Finset.mem_range.mp hi))]
    rw [← Finset.mul_sum, ← mul_assoc, hhalf]
    congr 1
  · funext c
    simp only [dftN]
    rw [congrArg Finset.range hs, Finset.sum_range_add]
    rw [hdiv]
    rw [show (2 : ℕ) * (2 * r / t) * l = (2 * r / t) * (2 * l) by ring]
    have hterm : ∀ i : ℕ, i < t / 2 →
        yMul r (sgn * (((2 * r / t * (2 * l + 1)) * (t / 2 + i) : ℕ) : ℤ)) (a (t / 2 + i)) c
          = - yMul r (sgn * (((2 * r / t * (2 * l + 1)) * i : ℕ) : ℤ)) (a (i + t / 2)) c := by
      intro i hi
      rw [show t / 2 + i = i + t / 2 by omega]
      have hnat : (2 * r / t * (2 * l + 1)) * (i + t / 2) = (2 * r / t * (2 * l + 1)) * i + (2 * l + 1) * r := by
        rw [mul_add, show 2 * r / t * (2 * l + 1) * (t / 2) = (2 * l + 1) * r by
          rw [show 2 * r / t * (2 * l + 1) * (t / 2) = (2 * l + 1) * ((2 * r / t) * (t / 2)) by ring,
            hmul]]
      calc yMul r (sgn * (((2 * r / t * (2 * l + 1)) * (i + t / 2) : ℕ) : ℤ)) (a (i + t / 2)) c
          = yMul r (sgn * ((((2 * r / t * (2 * l + 1)) * i + (2 * l + 1) * r : ℕ)) : ℤ)) (a (i + t / 2)) c := by
            rw [hnat]
        _ = yMul r (sgn * (((2 * r / t * (2 * l + 1)) * i : ℕ) : ℤ) + sgn * (((2 * l + 1) * r : ℕ) : ℤ))
              (a (i + t / 2)) c := by rw [Nat.cast_add, mul_add]
        _ = yMul r (sgn * (((2 * r / t * (2 * l + 1)) * i : ℕ) : ℤ))
              (yMul r (sgn * (((2 * l + 1) * r : ℕ) : ℤ)) (a (i + t / 2))) c := by rw [hcomp]
        _ = yMul r (sgn * (((2 * r / t * (2 * l + 1)) * i : ℕ) : ℤ)) (-(a (i + t / 2))) c := by
              rw [yMul_sgn_odd hr hsgn l]
        _ = - yMul r (sgn * (((2 * r / t * (2 * l + 1)) * i : ℕ) : ℤ)) (a (i + t / 2)) c := by
              rw [yMul_neg_apply hr]
    rw [Finset.sum_congr rfl (fun i hi => hterm i (Finset.mem_range.mp hi))]
    rw [← Finset.sum_add_distrib]
    have hkey : ∀ i : ℕ, i < t / 2 →
        yMul r (sgn * (((2 * r / t * (2 * l + 1)) * i : ℕ) : ℤ)) (a i) c
          + (- yMul r (sgn * (((2 * r / t * (2 * l + 1)) * i : ℕ) : ℤ)) (a (i + t / 2)) c)
          = 2 * (yMul r (sgn * (((2 * r / t * (2 * l + 1)) * i : ℕ) : ℤ))
              ((a i - a (i + t / 2)) / 2) c) := by
      intro i hi
      rw [← yMul_neg_apply hr, yMul_add_apply hr, yMul_half hr, ← sub_eq_add_neg]
    rw [Finset.sum_congr rfl (fun i hi => hkey i (Finset.mem_range.mp hi))]
    rw [← Finset.mul_sum, ← mul_assoc, hhalf]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [show (fun c => yMul r (sgn * (((2 * r / t) * i : ℕ) : ℤ))
          (fun c' => (a i c' - a (i + t / 2) c') / 2) c)
        = yMul r (sgn * (((2 * r / t) * i : ℕ) : ℤ))
          (fun c' => (a i c' - a (i + t / 2) c') / 2) from rfl,
      ← hcomp, ← mul_add, ← Nat.cast_add]
    rw [show ((2 * r / t * (2 * l)) * i + (2 * r / t) * i) = (2 * r / t * (2 * l + 1)) * i by ring]
    rfl

/-! ## Bit-reversal ordering of the radix-two level composition -/

section DftLevels
variable {r : ℕ}

/-- Zero levels of the recursion do nothing. -/
lemma levels_zero (sgn : ℤ) (t : ℕ) (a : Arr r) : levels r sgn t 0 a = a := rfl

/-- `bitrev 0` is zero. -/
lemma bitrev_zero (n : ℕ) : bitrev 0 n = 0 := by simp [bitrev]

/-- The length-`1` transform is the identity. -/
lemma dftN_one (hr : 0 < r) (sgn : ℤ) (b : Arr r) : dftN r 1 sgn b 0 = b 0 := by
  obtain ⟨-, hzero, -, -, -, -, -⟩ := yMulAlg r hr
  funext c
  simp [dftN, hzero]

end DftLevels

/-- **Bit-reversal ordering of the radix-two synthetic FFT.**  For `t = 2^k` dividing `2r`, the
`k` iterated butterfly stages of sizes `t, t/2, ..., 2` compute the length-`t` synthetic
transform of `a` in bit-reversed output order: the value at position `bitrev k j` is the
length-`t` transform at `j`. -/
theorem dftLevels (r : ℕ) (sgn : ℤ) (hr : 0 < r) (hsgn : sgn = 1 ∨ sgn = -1) :
    ∀ (k : ℕ) (t : ℕ), t = 2 ^ k → t ∣ 2 * r → ∀ (a : Arr r) (j : ℕ), j < t →
      dftN r t sgn a j = levels r sgn t k a (bitrev k j) := by
  intro k
  induction k with
  | zero =>
      intro t ht htr a j hj
      rw [pow_zero] at ht
      subst ht
      have hj0 : j = 0 := by omega
      subst hj0
      rw [dftN_one hr, levels_zero, bitrev_zero]
  | succ k ih =>
      obtain ⟨-, -, -, hb2, hb2o, -⟩ := bitrevFacts
      intro t ht htr a j hj
      have hsd : t / 2 = 2 ^ k := by rw [ht, two_pow_succ_div_two]
      have h2t : 2 * (t / 2) = t := by rw [hsd, ← pow_succ']; exact ht.symm
      have hdvd : t / 2 ∣ 2 * r := dvd_trans ⟨2, by rw [Nat.mul_comm]; exact h2t.symm⟩ htr
      have hj2 : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rcases hjmod : j % 2 with _ | _ | m
      · have hj' : j = 2 * (j / 2) := by omega
        have hl : j / 2 < t / 2 := by omega
        rw [hj', hb2 k (j / 2)]
        rw [(dftParts r t sgn hr hsgn ⟨k + 1, by omega, ht⟩ htr a (j / 2) hl).1]
        change dftN r (t / 2) sgn (fun k c => (a k c + a (k + t / 2) c) / 2) (j / 2) =
          levels r sgn (t / 2) k (lvlN r t sgn a) (bitrev k (j / 2))
        rw [ih (t / 2) hsd hdvd (fun k c => (a k c + a (k + t / 2) c) / 2) (j / 2) hl]
        exact levels_congr sgn k (t / 2) hsd (fun q hq => (lvlN_apply_left sgn t a q hq).symm)
          (bitrev k (j / 2)) (by rw [hsd]; exact bitrev_lt k (j / 2))
      · have hj' : j = 2 * (j / 2) + 1 := by omega
        have hl : j / 2 < t / 2 := by omega
        rw [hj', hb2o k (j / 2), ← hsd]
        rw [(dftParts r t sgn hr hsgn ⟨k + 1, by omega, ht⟩ htr a (j / 2) hl).2]
        change dftN r (t / 2) sgn (fun k c => yMul r (sgn * (((2 * r / t) * k : ℕ) : ℤ))
              (fun c' => (a k c' - a (k + t / 2) c') / 2) c) (j / 2) =
          levels r sgn (t / 2) k (lvlN r t sgn a) (t / 2 + bitrev k (j / 2))
        rw [show t / 2 + bitrev k (j / 2) = bitrev k (j / 2) + t / 2 by omega]
        rw [levels_shift_apply sgn k (t / 2) (t / 2) (lvlN r t sgn a) (fun jj hjj => by
          rw [hsd, Nat.pow_div (by omega : jj ≤ k) (by norm_num : 0 < 2)]
          exact Nat.pow_dvd_pow 2 (by omega : k - jj ≤ k)) (bitrev k (j / 2))]
        rw [ih (t / 2) hsd hdvd (fun k c => yMul r (sgn * (((2 * r / t) * k : ℕ) : ℤ))
              (fun c' => (a k c' - a (k + t / 2) c') / 2) c) (j / 2) hl]
        exact levels_congr sgn k (t / 2) hsd
          (fun q hq => (lvlN_apply_right sgn t a q hq).symm) (bitrev k (j / 2))
          (by rw [hsd]; exact bitrev_lt k (j / 2))
      · omega

theorem dft1Math (r t : ℕ) (sgn : ℤ) (hr : 0 < r) (hsgn : sgn = 1 ∨ sgn = -1)
    (ht : ∃ k : ℕ, 1 ≤ k ∧ t = 2 ^ k) (htr : t ∣ 2 * r) :
    (∀ (a : Arr r) (p : ℕ), p < t →
      levels r sgn t (Nat.log 2 t) a p = dftN r t sgn a (bitrev (Nat.log 2 t) p)) ∧
    (∀ (a : Arr r) (l : ℕ), l < t / 2 →
      dftN r t sgn a (2 * l) =
        dftN r (t / 2) sgn (fun k c => (a k c + a (k + t / 2) c) / 2) l ∧
      dftN r t sgn a (2 * l + 1) =
        dftN r (t / 2) sgn (fun k c =>
          HvdH.yMul r (sgn * (((2 * r / t) * k : ℕ) : ℤ))
            (fun c' => (a k c' - a (k + t / 2) c') / 2) c) l) := by
  obtain ⟨k, hk1, htk⟩ := ht
  refine ⟨?_, dftParts r t sgn hr hsgn ⟨k, hk1, htk⟩ htr⟩
  intro a p hp
  have hlog : Nat.log 2 t = k := by rw [htk]; exact Nat.log_pow (by norm_num) k
  have hp' : p < 2 ^ k := by rw [← htk]; exact hp
  rw [hlog]
  exact (congrArg (levels r sgn t k a) (bitrev_invol k p hp').symm).trans
    (dftLevels r sgn hr hsgn k t htk htr a (bitrev k p) (by rw [htk]; exact bitrev_lt k p)).symm

end Work.SynFFT
