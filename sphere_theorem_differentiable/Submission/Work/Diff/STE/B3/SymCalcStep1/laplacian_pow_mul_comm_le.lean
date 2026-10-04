import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalcStep1.Defs
import Submission.Work.Diff.STE.B3.SymCalcStep1.conv_summable_of_moment_bound
import Submission.Work.Diff.STE.summable_conv_nonneg_tsum
import Submission.Work.Diff.STE.tsum_mul_sq_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Symbol calculus, step 1: the Leibniz estimate `[Λ^k, M_a]` is of order `2k - 1`

This is PIECE 0 of the symbol calculus described in `Submission/Work/Diff/STE/B3/SymCalc.lean`.
On the Fourier side, `Λ^k` is the multiplier with symbol `λ(m) = Σⱼ (2π mⱼ)²` raised to the `k`-th
power (`Work.Diff.STE.B3.SymCalcStep1.cLam k`) and `M_a` is the convolution `conv a`; the
commutator is the family

  `m ↦ λ(m)^k · (a * c)(m) − (a * (λ^k · c))(m) = Σ'_j a (m − j) · (λ(m)^k − λ(j)^k) · c j`,

a discrete "differential operator of order `2k − 1`", i.e. it loses exactly `2k − 1` derivatives:

  `CSq s ([Λ^k, M_a] c) ≤ C · CSq (s + 2k − 1) c`.

The proof is the standard two-step one.  Writing `A l = ⟨l⟩^{s+2k} ‖a l‖` and
`B j = ⟨j⟩^{s+2k−1} ‖c j‖²` (`⟨k⟩² = wt k`), the pointwise bound
`⟨m⟩^{s} |λ(m)^k − λ(j)^k|² ≤ C₁ ⟨m−j⟩^{s+2k} ⟨j⟩^{s+2k−1}` (delegated, `lam_pow_sub_sq_le`)
gives, by Cauchy–Schwarz in the summation index and the discrete Tonelli theorem
(`summable_conv_nonneg_tsum`),

  `⟨m⟩^s ‖[Λ^k, M_a] c (m)‖² ≤ (∑ ‖a‖) C₁ ∑_j A(m−j) B j`,

and summing over `m` produces the product of the two masses `∑ A = ∑ ⟨l⟩^{s+2k}‖a l‖` and
`∑ B = CSq (s+2k−1) c`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.SymCalcStep1

private lemma sym_wt_neg {ι : Type*} [Fintype ι] (l : ι → ℤ) :
    Work.Diff.STE.wt (-l) = Work.Diff.STE.wt l := by
  simp only [Work.Diff.STE.wt, Pi.neg_apply, Int.cast_neg, neg_sq]

/-- The slowly varying inequality in the direction needed for the tail index:
`⟨m − l⟩ ≤ 2 ⟨m⟩ ⟨l⟩`. -/
private lemma sym_wt_sub_le {ι : Type*} [Fintype ι] (m l : ι → ℤ) :
    Work.Diff.STE.wt (m - l) ≤ 2 * (Work.Diff.STE.wt m * Work.Diff.STE.wt l) := by
  have h := Work.Diff.STE.wt_le_two_mul (m - l) m
  have h2 : (m - l) - m = -l := by abel
  rw [h2, sym_wt_neg] at h
  exact h

/-- **The commutator identity.**  For coefficient families `a`, `φ`, `c` and a frequency `m`, if the
two convolution sums converge then

  `φ m · (a * c)(m) − (a * (φ · c))(m) = Σ'_l a l · (φ m − φ (m − l)) · c (m − l)`. -/
private lemma sym_conv_sub_comm_tsum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a φ c : (ι → ℤ) → ℂ) (m : ι → ℤ)
    (h1 : Summable (fun l : ι → ℤ => a l * c (m - l)))
    (h2 : Summable (fun l : ι → ℤ => a l * (φ (m - l) * c (m - l)))) :
    φ m * Work.Diff.STE.conv a c m - Work.Diff.STE.conv a (fun j => φ j * c j) m
      = ∑' l : ι → ℤ, a l * ((φ m - φ (m - l)) * c (m - l)) := by
  have h2' : Summable (fun l : ι → ℤ => φ m * (a l * c (m - l))) := h1.mul_left (φ m)
  rw [Work.Diff.STE.conv, Work.Diff.STE.conv, ← tsum_mul_left]
  rw [← Summable.tsum_sub h2' h2]
  exact tsum_congr fun l => by ring

/-! ### The pointwise symbol estimate

Everything below is self-contained: it only uses `lam m = Σⱼ (2π mⱼ)²`, `wt m = 1 + Σⱼ mⱼ²` and
Peetre's inequality `wt m ≤ 2 wt (m - j) wt j`. -/

private lemma sym_sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

private lemma sym_sum_sq_sub_le_wt_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m j : ι → ℤ) :
    (∑ i, ((((m i : ℤ)) : ℝ) - ((j i : ℤ) : ℝ)) ^ 2) ≤ Work.Diff.STE.wt (m - j) := by
  have h : (∑ i, ((((m i : ℤ)) : ℝ) - ((j i : ℤ) : ℝ)) ^ 2)
      = ∑ i, ((((m - j) i : ℤ)) : ℝ) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.sub_apply]
    push_cast
    ring
  rw [h]
  exact sum_sq_le_wt (m - j)

private lemma sym_sum_sq_add_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m j : ι → ℤ) :
    (∑ i, ((((m i : ℤ)) : ℝ) + ((j i : ℤ) : ℝ)) ^ 2)
      ≤ 2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j) := by
  have h1 : ∀ i, ((((m i : ℤ)) : ℝ) + ((j i : ℤ) : ℝ)) ^ 2
      ≤ 2 * ((((m i : ℤ)) : ℝ)) ^ 2 + 2 * ((((j i : ℤ)) : ℝ)) ^ 2 :=
    fun i => sym_sq_add_le_two _ _
  have h2 : (∑ i, (2 * ((((m i : ℤ)) : ℝ)) ^ 2 + 2 * ((((j i : ℤ)) : ℝ)) ^ 2))
      = 2 * (∑ i, ((((m i : ℤ)) : ℝ)) ^ 2) + 2 * (∑ i, ((((j i : ℤ)) : ℝ)) ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hm := sum_sq_le_wt m
  have hj := sum_sq_le_wt j
  calc (∑ i, ((((m i : ℤ)) : ℝ) + ((j i : ℤ) : ℝ)) ^ 2)
      ≤ ∑ i, (2 * ((((m i : ℤ)) : ℝ)) ^ 2 + 2 * ((((j i : ℤ)) : ℝ)) ^ 2) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = 2 * (∑ i, ((((m i : ℤ)) : ℝ)) ^ 2) + 2 * (∑ i, ((((j i : ℤ)) : ℝ)) ^ 2) := h2
    _ ≤ 2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j) := by linarith

/-- `|λ(m) − λ(j)|² ≤ (2π)⁴ · 2 · ⟨m−j⟩ (⟨m⟩ + ⟨j⟩)`. -/
private lemma sym_lam_sub_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (m j : ι → ℤ) :
    (lam m - lam j) ^ 2
      ≤ (2 * Real.pi) ^ 4 * 2
          * (Work.Diff.STE.wt (m - j) * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)) := by
  have h1 : lam m - lam j
      = (2 * Real.pi) ^ 2 * ∑ i, ((((m i : ℤ)) : ℝ) - ((j i : ℤ) : ℝ))
          * ((((m i : ℤ)) : ℝ) + ((j i : ℤ) : ℝ)) := by
    rw [lam_eq m, lam_eq j, ← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hcs : (∑ i, ((((m i : ℤ)) : ℝ) - ((j i : ℤ) : ℝ))
        * ((((m i : ℤ)) : ℝ) + ((j i : ℤ) : ℝ))) ^ 2
      ≤ (∑ i, ((((m i : ℤ)) : ℝ) - ((j i : ℤ) : ℝ)) ^ 2)
        * (∑ i, ((((m i : ℤ)) : ℝ) + ((j i : ℤ) : ℝ)) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hpn : (0 : ℝ) ≤ ((2 * Real.pi) ^ 2) ^ 2 := by positivity
  have hlast : ((2 * Real.pi) ^ 2) ^ 2 * (Work.Diff.STE.wt (m - j)
        * (2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)))
      = (2 * Real.pi) ^ 4 * 2
          * (Work.Diff.STE.wt (m - j) * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)) := by ring
  have h3 : ((2 * Real.pi) ^ 2) ^ 2
        * ((∑ i, ((((m i : ℤ)) : ℝ) - ((j i : ℤ) : ℝ)) ^ 2)
          * (∑ i, ((((m i : ℤ)) : ℝ) + ((j i : ℤ) : ℝ)) ^ 2))
      ≤ ((2 * Real.pi) ^ 2) ^ 2
        * (Work.Diff.STE.wt (m - j) * (2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j))) := by
    refine mul_le_mul_of_nonneg_left ?_ hpn
    exact mul_le_mul (sym_sum_sq_sub_le_wt_sub m j) (sym_sum_sq_add_le m j) (by positivity)
      (le_of_lt (wt_pos (m - j)))
  calc (lam m - lam j) ^ 2
      = ((2 * Real.pi) ^ 2) ^ 2
          * (∑ i, ((((m i : ℤ)) : ℝ) - ((j i : ℤ) : ℝ))
              * ((((m i : ℤ)) : ℝ) + ((j i : ℤ) : ℝ))) ^ 2 := by
        rw [h1, mul_pow]
    _ ≤ ((2 * Real.pi) ^ 2) ^ 2
          * ((∑ i, ((((m i : ℤ)) : ℝ) - ((j i : ℤ) : ℝ)) ^ 2)
            * (∑ i, ((((m i : ℤ)) : ℝ) + ((j i : ℤ) : ℝ)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hpn
    _ ≤ ((2 * Real.pi) ^ 2) ^ 2
          * (Work.Diff.STE.wt (m - j) * (2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j))) := h3
    _ = (2 * Real.pi) ^ 4 * 2
          * (Work.Diff.STE.wt (m - j) * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)) := hlast

/-- `(x^k − y^k)² ≤ k² (x+y)^{2k−2} (x−y)²` for `x, y ≥ 0`. -/
private lemma sym_pow_sub_sq_le (k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x ^ k - y ^ k) ^ 2 ≤ (k : ℝ) ^ 2 * (x + y) ^ (2 * k - 2) * (x - y) ^ 2 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  · have h := abs_pow_sub_pow_le x y k
    have hx0 : |x| = x := abs_of_nonneg hx
    have hy0 : |y| = y := abs_of_nonneg hy
    rw [hx0, hy0] at h
    have hsq : (x ^ k - y ^ k) ^ 2 ≤ (|x - y| * (k : ℝ) * max x y ^ (k - 1)) ^ 2 := by
      rw [← sq_abs (x ^ k - y ^ k)]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hmax : max x y ≤ x + y := max_le (le_add_of_nonneg_right hy) (le_add_of_nonneg_left hx)
    have hexp : 2 * k - 2 = 2 * (k - 1) := by omega
    have hmax2 : (max x y) ^ (2 * k - 2) ≤ (x + y) ^ (2 * k - 2) :=
      pow_le_pow_left₀ (le_trans hx (le_max_left x y)) hmax _
    have habs : |x - y| ^ 2 = (x - y) ^ 2 := sq_abs _
    calc (x ^ k - y ^ k) ^ 2
        ≤ (|x - y| * (k : ℝ) * max x y ^ (k - 1)) ^ 2 := hsq
      _ = (k : ℝ) ^ 2 * ((max x y) ^ (2 * (k - 1))) * (x - y) ^ 2 := by
          rw [mul_pow, mul_pow, ← pow_mul, habs]
          ring
      _ = (k : ℝ) ^ 2 * ((max x y) ^ (2 * k - 2)) * (x - y) ^ 2 := by
          rw [hexp]
      _ ≤ (k : ℝ) ^ 2 * ((x + y) ^ (2 * k - 2)) * (x - y) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax2 (by positivity))
            (sq_nonneg _)

/-- `(λ(m)^k − λ(j)^k)² ≤ k² ((2π)²(⟨m⟩+⟨j⟩))^{2k−2} · (2π)⁴·2·⟨m−j⟩(⟨m⟩+⟨j⟩)`. -/
private lemma sym_pow_diff_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (m j : ι → ℤ) :
    (lam m ^ k - lam j ^ k) ^ 2
      ≤ (k : ℝ) ^ 2
          * ((2 * Real.pi) ^ 2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)) ^ (2 * k - 2)
          * ((2 * Real.pi) ^ 4 * 2
              * (Work.Diff.STE.wt (m - j) * (Work.Diff.STE.wt m + Work.Diff.STE.wt j))) := by
  have hpow := sym_pow_sub_sq_le k (lam_nonneg m) (lam_nonneg j)
  have hsub := sym_lam_sub_sq_le m j
  have hsum : lam m + lam j
      ≤ (2 * Real.pi) ^ 2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j) := by
    have h1 := lam_le m
    have h2 := lam_le j
    linarith
  have hmax : (lam m + lam j) ^ (2 * k - 2)
      ≤ ((2 * Real.pi) ^ 2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)) ^ (2 * k - 2) :=
    pow_le_pow_left₀ (by linarith [lam_nonneg m, lam_nonneg j]) hsum _
  have hm0 : (0 : ℝ) ≤ Work.Diff.STE.wt m := le_of_lt (wt_pos m)
  have hj0 : (0 : ℝ) ≤ Work.Diff.STE.wt j := le_of_lt (wt_pos j)
  have hmj0 : (0 : ℝ) ≤ Work.Diff.STE.wt (m - j) := le_of_lt (wt_pos (m - j))
  have hXnn : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j) :=
    mul_nonneg (by positivity) (by linarith)
  have hann : (0 : ℝ) ≤ (k : ℝ) ^ 2
      * ((2 * Real.pi) ^ 2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)) ^ (2 * k - 2) :=
    mul_nonneg (sq_nonneg _) (pow_nonneg hXnn _)
  have hbnn : (0 : ℝ) ≤ (k : ℝ) ^ 2
      * ((2 * Real.pi) ^ 2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)) ^ (2 * k - 2)
      * ((2 * Real.pi) ^ 4 * 2
          * (Work.Diff.STE.wt (m - j) * (Work.Diff.STE.wt m + Work.Diff.STE.wt j))) :=
    mul_nonneg hann (mul_nonneg (mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) 4)
      (by norm_num : (0 : ℝ) ≤ 2)) (mul_nonneg hmj0 (by linarith)))
  exact hpow.trans (mul_le_mul (mul_le_mul_of_nonneg_left hmax (sq_nonneg _)) hsub
    (sq_nonneg _) hann)

/-- **The weighted pointwise symbol estimate.**  For every `k ≥ 0` and `s`, there is `C ≥ 0` with

  `⟨m⟩^{s} (λ(m)^k − λ(j)^k)² ≤ C ⟨m−j⟩^{s+2k} ⟨j⟩^{s+2k−1}`
  for all frequencies `m`, `j`. -/
private lemma sym_lam_pow_sub_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m j : ι → ℤ,
      (Work.Diff.STE.wt m) ^ s * (lam m ^ k - lam j ^ k) ^ 2
        ≤ C * (Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1) := by
  refine ⟨2 * (k : ℝ) ^ 2 * ((2 * Real.pi) ^ 4 * ((2 * Real.pi) ^ 2) ^ (2 * k - 2))
      * 3 ^ (2 * k - 1) * 2 ^ s, by positivity, ?_⟩
  intro m j
  have hA := sym_pow_diff_sq_le (ι := ι) k m j
  have hmnn : (0 : ℝ) ≤ Work.Diff.STE.wt m := le_of_lt (wt_pos m)
  have hjnn : (0 : ℝ) ≤ Work.Diff.STE.wt j := le_of_lt (wt_pos j)
  have hpnn : (0 : ℝ) ≤ Work.Diff.STE.wt (m - j) := le_of_lt (wt_pos (m - j))
  have hWnn : (0 : ℝ) ≤ Work.Diff.STE.wt m + Work.Diff.STE.wt j := by linarith
  have hpeetre : Work.Diff.STE.wt m ≤ 2 * (Work.Diff.STE.wt (m - j) * Work.Diff.STE.wt j) := by
    have h := wt_le_peetre m j
    linarith
  have h1 : (Work.Diff.STE.wt m) ^ s
      ≤ 2 ^ s * ((Work.Diff.STE.wt (m - j)) ^ s * (Work.Diff.STE.wt j) ^ s) := by
    calc (Work.Diff.STE.wt m) ^ s ≤ (2 * (Work.Diff.STE.wt (m - j) * Work.Diff.STE.wt j)) ^ s :=
          pow_le_pow_left₀ hmnn hpeetre s
      _ = 2 ^ s * ((Work.Diff.STE.wt (m - j)) ^ s * (Work.Diff.STE.wt j) ^ s) := by ring
  have h2 : (Work.Diff.STE.wt m + Work.Diff.STE.wt j) ^ (2 * k - 1)
      ≤ 3 ^ (2 * k - 1)
          * ((Work.Diff.STE.wt (m - j)) ^ (2 * k - 1) * (Work.Diff.STE.wt j) ^ (2 * k - 1)) := by
    have hle : Work.Diff.STE.wt m + Work.Diff.STE.wt j
        ≤ 3 * (Work.Diff.STE.wt (m - j) * Work.Diff.STE.wt j) := by
      have h1 := wt_one_le (m - j)
      nlinarith [wt_pos (m - j), wt_pos j]
    calc (Work.Diff.STE.wt m + Work.Diff.STE.wt j) ^ (2 * k - 1)
        ≤ (3 * (Work.Diff.STE.wt (m - j) * Work.Diff.STE.wt j)) ^ (2 * k - 1) :=
          pow_le_pow_left₀ hWnn hle _
      _ = 3 ^ (2 * k - 1)
            * ((Work.Diff.STE.wt (m - j)) ^ (2 * k - 1)
              * (Work.Diff.STE.wt j) ^ (2 * k - 1)) := by ring
  have hexp : s + (2 * k - 1) = s + 2 * k - 1 := by omega
  have hW : (Work.Diff.STE.wt m) ^ s * (Work.Diff.STE.wt m + Work.Diff.STE.wt j) ^ (2 * k - 1)
      ≤ 2 ^ s * 3 ^ (2 * k - 1)
          * ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k - 1)
              * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1)) := by
    calc (Work.Diff.STE.wt m) ^ s * (Work.Diff.STE.wt m + Work.Diff.STE.wt j) ^ (2 * k - 1)
        ≤ (2 ^ s * ((Work.Diff.STE.wt (m - j)) ^ s * (Work.Diff.STE.wt j) ^ s))
            * (3 ^ (2 * k - 1)
              * ((Work.Diff.STE.wt (m - j)) ^ (2 * k - 1)
                * (Work.Diff.STE.wt j) ^ (2 * k - 1))) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 ^ s * 3 ^ (2 * k - 1)
            * (((Work.Diff.STE.wt (m - j)) ^ s * (Work.Diff.STE.wt (m - j)) ^ (2 * k - 1))
              * ((Work.Diff.STE.wt j) ^ s * (Work.Diff.STE.wt j) ^ (2 * k - 1))) := by ring
      _ = 2 ^ s * 3 ^ (2 * k - 1)
            * ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k - 1)
              * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1)) := by
          rw [← pow_add, ← pow_add, hexp]
  have hidW : (Work.Diff.STE.wt m + Work.Diff.STE.wt j) ^ (2 * k - 2)
        * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)
      = (Work.Diff.STE.wt m + Work.Diff.STE.wt j) ^ (2 * k - 1) := by
    rw [← pow_succ]
    congr 1
    omega
  have hidP : Work.Diff.STE.wt (m - j) * (Work.Diff.STE.wt (m - j)) ^ (s + 2 * k - 1)
      = (Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) := by
    rw [← pow_succ']
    congr 1
    omega
  calc (Work.Diff.STE.wt m) ^ s * (lam m ^ k - lam j ^ k) ^ 2
      ≤ (Work.Diff.STE.wt m) ^ s
          * ((k : ℝ) ^ 2
            * ((2 * Real.pi) ^ 2 * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)) ^ (2 * k - 2)
            * ((2 * Real.pi) ^ 4 * 2
                * (Work.Diff.STE.wt (m - j)
                  * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)))) :=
        mul_le_mul_of_nonneg_left hA (pow_nonneg hmnn s)
    _ = (k : ℝ) ^ 2 * ((2 * Real.pi) ^ 4 * 2) * ((2 * Real.pi) ^ 2) ^ (2 * k - 2)
          * (Work.Diff.STE.wt (m - j)
            * ((Work.Diff.STE.wt m) ^ s
              * ((Work.Diff.STE.wt m + Work.Diff.STE.wt j) ^ (2 * k - 2)
                * (Work.Diff.STE.wt m + Work.Diff.STE.wt j)))) := by
        rw [mul_pow]
        ring
    _ = (k : ℝ) ^ 2 * ((2 * Real.pi) ^ 4 * 2) * ((2 * Real.pi) ^ 2) ^ (2 * k - 2)
          * (Work.Diff.STE.wt (m - j)
            * ((Work.Diff.STE.wt m) ^ s
              * (Work.Diff.STE.wt m + Work.Diff.STE.wt j) ^ (2 * k - 1))) := by
        rw [hidW]
    _ ≤ (k : ℝ) ^ 2 * ((2 * Real.pi) ^ 4 * 2) * ((2 * Real.pi) ^ 2) ^ (2 * k - 2)
          * (Work.Diff.STE.wt (m - j)
            * (2 ^ s * 3 ^ (2 * k - 1)
              * ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k - 1)
                * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW hpnn) (by positivity)
    _ = (k : ℝ) ^ 2 * ((2 * Real.pi) ^ 4 * 2) * ((2 * Real.pi) ^ 2) ^ (2 * k - 2)
          * 2 ^ s * 3 ^ (2 * k - 1)
          * ((Work.Diff.STE.wt (m - j)) * (Work.Diff.STE.wt (m - j)) ^ (s + 2 * k - 1)
            * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1)) := by ring
    _ = (2 * (k : ℝ) ^ 2 * ((2 * Real.pi) ^ 4 * ((2 * Real.pi) ^ 2) ^ (2 * k - 2))
          * 3 ^ (2 * k - 1) * 2 ^ s) * (Work.Diff.STE.wt (m - j)) ^ (s + 2 * k)
          * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1) := by
        rw [hidP]
        ring

theorem laplacian_pow_mul_comm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : (ι → ℤ) → ℂ)
    (ha : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖a k‖))
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ c : (ι → ℤ) → ℂ,
        Summable (fun m : ι → ℤ =>
            (Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖c m‖ ^ 2) →
        Work.Diff.STE.CSq s
            (fun m => (((∑ j, (2 * Real.pi * (m j : ℝ)) ^ 2) ^ k : ℝ) : ℂ)
                * Work.Diff.STE.conv a c m
              - Work.Diff.STE.conv a (fun m =>
                  (((∑ j, (2 * Real.pi * (m j : ℝ)) ^ 2) ^ k : ℝ) : ℂ) * c m) m)
          ≤ C * Work.Diff.STE.CSq (s + 2 * k - 1) c := by
  classical
  obtain ⟨C1, hC1nn, hC1⟩ := sym_lam_pow_sub_sq_le (ι := ι) k hk s
  set L1 : ℝ := ∑' l : ι → ℤ, ‖a l‖ with hL1def
  set Lw : ℝ := ∑' l : ι → ℤ, (Work.Diff.STE.wt l) ^ (s + 2 * k) * ‖a l‖ with hLwdef
  have hL1nn : 0 ≤ L1 := by
    rw [hL1def]; exact tsum_nonneg fun l => norm_nonneg _
  have hLwnn : 0 ≤ Lw := by
    rw [hLwdef]
    exact tsum_nonneg fun l => mul_nonneg (pow_nonneg (le_of_lt (wt_pos l)) _) (norm_nonneg _)
  refine ⟨L1 * C1 * Lw, by positivity, ?_⟩
  intro c hc
  -- `c ∈ ℓ²`
  have hc0 : Summable (fun m : ι → ℤ => ‖c m‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_) hc
    have h1 : (1 : ℝ) ≤ (Work.Diff.STE.wt m) ^ (s + 2 * k - 1) := one_le_pow₀ (wt_one_le m)
    calc ‖c m‖ ^ 2 = 1 * ‖c m‖ ^ 2 := (one_mul _).symm
      _ ≤ (Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖c m‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hcc : ∀ j : ι → ℤ, ‖c j‖ ≤ Real.sqrt (∑' j : ι → ℤ, ‖c j‖ ^ 2) := by
    intro j
    refine (Real.le_sqrt (norm_nonneg _) (tsum_nonneg fun i => sq_nonneg _)).mpr ?_
    exact hc0.le_tsum j (fun i _ => sq_nonneg _)
  have hφb : ∀ j : ι → ℤ, ‖cLam k j‖ ≤ (2 * Real.pi) ^ (2 * k) * (Work.Diff.STE.wt j) ^ k := by
    intro j
    rw [cLam_norm]
    calc lam j ^ k ≤ ((2 * Real.pi) ^ 2 * Work.Diff.STE.wt j) ^ k :=
          pow_le_pow_left₀ (lam_nonneg j) (lam_le j) k
      _ = (2 * Real.pi) ^ (2 * k) * (Work.Diff.STE.wt j) ^ k := by rw [mul_pow, ← pow_mul]
  have ha0 : Summable (fun l : ι → ℤ => ‖a l‖) := by simpa using ha 0
  have hak : Summable (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ k * ‖a l‖) := by simpa using ha k
  -- the estimate at a single frequency
  have hPoint : ∀ m : ι → ℤ,
      (Work.Diff.STE.wt m) ^ s
          * ‖cLam k m * Work.Diff.STE.conv a c m
              - Work.Diff.STE.conv a (fun j => cLam k j * c j) m‖ ^ 2
        ≤ L1 * C1 * ∑' j : ι → ℤ,
            ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
              * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2) := by
    intro m
    let e : (ι → ℤ) ≃ (ι → ℤ) :=
      { toFun := fun j => m - j, invFun := fun j => m - j,
        left_inv := fun j => by simp [sub_sub_self],
        right_inv := fun j => by simp [sub_sub_self] }
    have hre : ∀ (g : (ι → ℤ) → ℝ), Summable g → Summable (fun j : ι → ℤ => g (m - j)) := by
      intro g hg
      simpa [Function.comp_def, e] using (Equiv.summable_iff e).mpr hg
    have h1m : Summable (fun l : ι → ℤ => a l * c (m - l)) :=
      (conv_summable_of_moment_bound a c (fun _ => 1) ha hc0 1 0 (fun j => by simp) m).congr
        (fun l => by ring)
    have h2m : Summable (fun l : ι → ℤ => a l * (cLam k (m - l) * c (m - l))) :=
      conv_summable_of_moment_bound a c (cLam k) ha hc0 ((2 * Real.pi) ^ (2 * k)) k hφb m
    have hid1 : cLam k m * Work.Diff.STE.conv a c m
          - Work.Diff.STE.conv a (fun j => cLam k j * c j) m
        = ∑' l : ι → ℤ, a l * ((cLam k m - cLam k (m - l)) * c (m - l)) :=
      sym_conv_sub_comm_tsum a (cLam k) c m h1m h2m
    have hid2 : cLam k m * Work.Diff.STE.conv a c m
          - Work.Diff.STE.conv a (fun j => cLam k j * c j) m
        = ∑' j : ι → ℤ, a (m - j) * ((cLam k m - cLam k j) * c j) := by
      rw [hid1]
      have hiff := Equiv.tsum_eq e
        (fun l : ι → ℤ => a l * ((cLam k m - cLam k (m - l)) * c (m - l)))
      rw [← hiff]
      refine tsum_congr fun i => ?_
      show a (m - i) * ((cLam k m - cLam k (m - (m - i))) * c (m - (m - i)))
        = a (m - i) * ((cLam k m - cLam k i) * c i)
      rw [sub_sub_self]
    -- summability of the summands, hence the norm bound
    have hFsum : Summable (fun j : ι → ℤ =>
        ‖a (m - j) * ((cLam k m - cLam k j) * c j)‖) := by
      have hg : Summable (fun j : ι → ℤ =>
          Real.sqrt (∑' l : ι → ℤ, ‖c l‖ ^ 2) * (‖cLam k m‖
              + (2 * Real.pi) ^ (2 * k) * 2 ^ k * (Work.Diff.STE.wt m) ^ k
                * (Work.Diff.STE.wt (m - j)) ^ k) * ‖a (m - j)‖) := by
        have hA1 : Summable (fun j : ι → ℤ => ‖a (m - j)‖) := hre _ ha0
        have hA2 : Summable (fun j : ι → ℤ => (Work.Diff.STE.wt (m - j)) ^ k * ‖a (m - j)‖) :=
          hre _ hak
        have h1 := hA1.mul_left (Real.sqrt (∑' l : ι → ℤ, ‖c l‖ ^ 2) * ‖cLam k m‖)
        have h2 := hA2.mul_left (Real.sqrt (∑' l : ι → ℤ, ‖c l‖ ^ 2)
            * ((2 * Real.pi) ^ (2 * k) * 2 ^ k * (Work.Diff.STE.wt m) ^ k))
        refine (h1.add h2).congr (fun j => ?_)
        ring
      refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hg
      have hb1 : ‖cLam k m - cLam k j‖
          ≤ ‖cLam k m‖ + (2 * Real.pi) ^ (2 * k) * (Work.Diff.STE.wt j) ^ k :=
        (norm_sub_le _ _).trans (add_le_add (le_refl _) (hφb j))
      have hb2 : (Work.Diff.STE.wt j) ^ k
          ≤ 2 ^ k * (Work.Diff.STE.wt m) ^ k * (Work.Diff.STE.wt (m - j)) ^ k := by
        have hwt : Work.Diff.STE.wt j
            ≤ 2 * (Work.Diff.STE.wt m * Work.Diff.STE.wt (j - m)) := Work.Diff.STE.wt_le_two_mul j m
        have hjm : Work.Diff.STE.wt (j - m) = Work.Diff.STE.wt (m - j) := by
          have : j - m = -(m - j) := by abel
          rw [this, sym_wt_neg]
        rw [hjm] at hwt
        calc (Work.Diff.STE.wt j) ^ k
            ≤ (2 * (Work.Diff.STE.wt m * Work.Diff.STE.wt (m - j))) ^ k :=
              pow_le_pow_left₀ (le_of_lt (wt_pos j)) hwt k
          _ = 2 ^ k * (Work.Diff.STE.wt m) ^ k * (Work.Diff.STE.wt (m - j)) ^ k := by ring
      calc ‖a (m - j) * ((cLam k m - cLam k j) * c j)‖
          = ‖a (m - j)‖ * (‖cLam k m - cLam k j‖ * ‖c j‖) := by rw [norm_mul, norm_mul]
        _ ≤ ‖a (m - j)‖ * ((‖cLam k m‖ + (2 * Real.pi) ^ (2 * k) * (Work.Diff.STE.wt j) ^ k)
              * Real.sqrt (∑' l : ι → ℤ, ‖c l‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            exact mul_le_mul hb1 (hcc j) (norm_nonneg _)
              (add_nonneg (norm_nonneg _) (mul_nonneg (by positivity)
                (pow_nonneg (le_of_lt (wt_pos j)) _)))
        _ ≤ ‖a (m - j)‖ * ((‖cLam k m‖ + (2 * Real.pi) ^ (2 * k)
              * (2 ^ k * (Work.Diff.STE.wt m) ^ k * (Work.Diff.STE.wt (m - j)) ^ k))
              * Real.sqrt (∑' l : ι → ℤ, ‖c l‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
              (norm_nonneg _)
            exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hb2 (by positivity))
        _ = Real.sqrt (∑' l : ι → ℤ, ‖c l‖ ^ 2) * (‖cLam k m‖
              + (2 * Real.pi) ^ (2 * k) * 2 ^ k * (Work.Diff.STE.wt m) ^ k
                * (Work.Diff.STE.wt (m - j)) ^ k) * ‖a (m - j)‖ := by ring
    have hSnorm : ‖cLam k m * Work.Diff.STE.conv a c m
          - Work.Diff.STE.conv a (fun j => cLam k j * c j) m‖
        ≤ ∑' j : ι → ℤ, ‖a (m - j)‖ * |lam m ^ k - lam j ^ k| * ‖c j‖ := by
      rw [hid2]
      have heq : (∑' i : ι → ℤ, ‖a (m - i) * ((cLam k m - cLam k i) * c i)‖)
          = ∑' j : ι → ℤ, ‖a (m - j)‖ * |lam m ^ k - lam j ^ k| * ‖c j‖ := by
        refine tsum_congr fun j => ?_
        rw [norm_mul, norm_mul, cLam_sub, dlam_norm]
        ring
      exact (norm_tsum_le_tsum_norm hFsum).trans heq.le
    -- Cauchy–Schwarz in the summation index
    set S : ℝ := ∑' j : ι → ℤ, ‖a (m - j)‖ * |lam m ^ k - lam j ^ k| * ‖c j‖ with hSdef
    have hCS : S ^ 2 ≤ L1 * ∑' j : ι → ℤ,
        ‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2 := by
      have hw : ∀ j : ι → ℤ, 0 ≤ ‖a (m - j)‖ := fun j => norm_nonneg _
      have hf : ∀ j : ι → ℤ, 0 ≤ |lam m ^ k - lam j ^ k| * ‖c j‖ :=
        fun j => mul_nonneg (abs_nonneg _) (norm_nonneg _)
      have hw' : Summable (fun j : ι → ℤ => ‖a (m - j)‖) := hre _ ha0
      have hf' : Summable (fun j : ι → ℤ =>
          ‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2) := by
        refine Summable.of_nonneg_of_le
          (f := fun j : ι → ℤ => (C1 / (Work.Diff.STE.wt m) ^ s) *
            (((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
              * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2)))
          (fun j => mul_nonneg (norm_nonneg _) (sq_nonneg _)) (fun j => ?_) ?_
        · have hb := hC1 m j
          have hwm : (0 : ℝ) < (Work.Diff.STE.wt m) ^ s := pow_pos (wt_pos m) s
          have hb' : (lam m ^ k - lam j ^ k) ^ 2
              ≤ C1 * ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k)
                  * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1)) / (Work.Diff.STE.wt m) ^ s := by
            rw [le_div_iff₀ hwm]
            calc (lam m ^ k - lam j ^ k) ^ 2 * (Work.Diff.STE.wt m) ^ s
                = (Work.Diff.STE.wt m) ^ s * (lam m ^ k - lam j ^ k) ^ 2 := by ring
              _ ≤ C1 * (Work.Diff.STE.wt (m - j)) ^ (s + 2 * k)
                    * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1) := hb
              _ = C1 * ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k)
                    * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1)) := by ring
          calc ‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2
              = ‖a (m - j)‖ * ((lam m ^ k - lam j ^ k) ^ 2 * ‖c j‖ ^ 2) := by
                rw [mul_pow, sq_abs]
            _ ≤ ‖a (m - j)‖ * ((C1 * ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k)
                    * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1)) / (Work.Diff.STE.wt m) ^ s)
                  * ‖c j‖ ^ 2) := by
                refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb' (sq_nonneg _))
                  (norm_nonneg _)
            _ = (C1 / (Work.Diff.STE.wt m) ^ s)
                  * (((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
                      * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2)) := by ring
        · exact (Work.Diff.STE.summable_conv_nonneg_tsum
            (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ (s + 2 * k) * ‖a l‖)
            (fun j : ι → ℤ => (Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2)
            (fun l => mul_nonneg (pow_nonneg (le_of_lt (wt_pos l)) _) (norm_nonneg _))
            (fun j => mul_nonneg (pow_nonneg (le_of_lt (wt_pos j)) _) (sq_nonneg _))
            (by simpa using ha (s + 2 * k)) hc).1 m |>.mul_left (C1 / (Work.Diff.STE.wt m) ^ s)
      have hmain := Work.Diff.STE.tsum_mul_sq_le (fun j : ι → ℤ => ‖a (m - j)‖)
        (fun j : ι → ℤ => |lam m ^ k - lam j ^ k| * ‖c j‖) hw hf hw' hf'
      calc S ^ 2 = (∑' j : ι → ℤ, ‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖)) ^ 2 := by
            rw [hSdef]; exact congrArg (· ^ 2) (tsum_congr fun j => by ring)
        _ ≤ (∑' j : ι → ℤ, ‖a (m - j)‖)
              * (∑' j : ι → ℤ, ‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2) := hmain
        _ = L1 * ∑' j : ι → ℤ, ‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2 := by
            rw [hL1def]
            congr 1
            exact Equiv.tsum_eq e (fun l : ι → ℤ => ‖a l‖)
    -- multiply by the weight `⟨m⟩^{2s}`
    have hT : (Work.Diff.STE.wt m) ^ s
          * (∑' j : ι → ℤ, ‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2)
        ≤ C1 * ∑' j : ι → ℤ,
            ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
              * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2) := by
      rw [← tsum_mul_left]
      have hsumR : Summable (fun j : ι → ℤ =>
          C1 * (((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
              * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2))) :=
        ((Work.Diff.STE.summable_conv_nonneg_tsum
          (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ (s + 2 * k) * ‖a l‖)
          (fun j : ι → ℤ => (Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2)
          (fun l => mul_nonneg (pow_nonneg (le_of_lt (wt_pos l)) _) (norm_nonneg _))
          (fun j => mul_nonneg (pow_nonneg (le_of_lt (wt_pos j)) _) (sq_nonneg _))
          (by simpa using ha (s + 2 * k)) hc).1 m).mul_left C1
      have hsumL : Summable (fun j : ι → ℤ =>
          (Work.Diff.STE.wt m) ^ s
            * (‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2)) := by
        refine Summable.of_nonneg_of_le
          (fun j => mul_nonneg (pow_nonneg (le_of_lt (wt_pos m)) _)
            (mul_nonneg (norm_nonneg _) (sq_nonneg _)))
          (fun j => ?_) hsumR
        have hb := hC1 m j
        calc (Work.Diff.STE.wt m) ^ s
              * (‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2)
            = ‖a (m - j)‖
                * (((Work.Diff.STE.wt m) ^ s * (lam m ^ k - lam j ^ k) ^ 2) * ‖c j‖ ^ 2) := by
              rw [mul_pow, sq_abs]; ring
          _ ≤ ‖a (m - j)‖ * ((C1 * (Work.Diff.STE.wt (m - j)) ^ (s + 2 * k)
                  * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1)) * ‖c j‖ ^ 2) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (sq_nonneg _))
                (norm_nonneg _)
          _ = C1 * (((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
                  * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2)) := by ring
      refine (Summable.tsum_le_tsum (fun j => ?_) hsumL hsumR).trans (le_of_eq ?_)
      · have hb := hC1 m j
        calc (Work.Diff.STE.wt m) ^ s
              * (‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2)
            = ‖a (m - j)‖
                * (((Work.Diff.STE.wt m) ^ s * (lam m ^ k - lam j ^ k) ^ 2) * ‖c j‖ ^ 2) := by
              rw [mul_pow, sq_abs]; ring
          _ ≤ ‖a (m - j)‖ * ((C1 * (Work.Diff.STE.wt (m - j)) ^ (s + 2 * k)
                  * (Work.Diff.STE.wt j) ^ (s + 2 * k - 1)) * ‖c j‖ ^ 2) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (sq_nonneg _))
                (norm_nonneg _)
          _ = C1 * (((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
                  * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2)) := by ring
      · rw [tsum_mul_left]
    -- assemble at frequency `m`
    have hstep : (Work.Diff.STE.wt m) ^ s
          * ‖cLam k m * Work.Diff.STE.conv a c m
              - Work.Diff.STE.conv a (fun j => cLam k j * c j) m‖ ^ 2
        ≤ L1 * C1 * ∑' j : ι → ℤ,
            ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
              * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2) := by
      have h1 : (Work.Diff.STE.wt m) ^ s
            * ‖cLam k m * Work.Diff.STE.conv a c m
                - Work.Diff.STE.conv a (fun j => cLam k j * c j) m‖ ^ 2
          ≤ (Work.Diff.STE.wt m) ^ s * S ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt (wt_pos m)) _)
        rw [hSdef]
        exact pow_le_pow_left₀ (norm_nonneg _) hSnorm 2
      have h2 : (Work.Diff.STE.wt m) ^ s * S ^ 2
          ≤ L1 * (Work.Diff.STE.wt m) ^ s
              * (∑' j : ι → ℤ, ‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2) := by
        rw [hSdef] at hCS
        have hTnn : 0 ≤ ∑' j : ι → ℤ,
            ‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2 :=
          tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (sq_nonneg _)
        nlinarith [hCS, hL1nn, pow_pos (wt_pos m) s, hTnn]
      calc (Work.Diff.STE.wt m) ^ s
            * ‖cLam k m * Work.Diff.STE.conv a c m
                - Work.Diff.STE.conv a (fun j => cLam k j * c j) m‖ ^ 2
          ≤ (Work.Diff.STE.wt m) ^ s * S ^ 2 := h1
        _ ≤ L1 * (Work.Diff.STE.wt m) ^ s
              * (∑' j : ι → ℤ, ‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2) := h2
        _ = L1 * ((Work.Diff.STE.wt m) ^ s
              * (∑' j : ι → ℤ, ‖a (m - j)‖ * (|lam m ^ k - lam j ^ k| * ‖c j‖) ^ 2)) := by ring
        _ ≤ L1 * (C1 * ∑' j : ι → ℤ,
              ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
                * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hT hL1nn
        _ = L1 * C1 * ∑' j : ι → ℤ,
              ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
                * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2) := by ring
    exact hstep
  -- summation over the frequency
  have hAB := Work.Diff.STE.summable_conv_nonneg_tsum
    (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ (s + 2 * k) * ‖a l‖)
    (fun j : ι → ℤ => (Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2)
    (fun l => mul_nonneg (pow_nonneg (le_of_lt (wt_pos l)) _) (norm_nonneg _))
    (fun j => mul_nonneg (pow_nonneg (le_of_lt (wt_pos j)) _) (sq_nonneg _))
    (by simpa using ha (s + 2 * k)) hc
  have hsumL : Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ s
      * ‖cLam k m * Work.Diff.STE.conv a c m
          - Work.Diff.STE.conv a (fun j => cLam k j * c j) m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (le_of_lt (wt_pos m)) _) (sq_nonneg _))
      (fun m => hPoint m) (hAB.2.1.mul_left (L1 * C1))
  have hsumR : Summable (fun m : ι → ℤ => L1 * C1 * ∑' j : ι → ℤ,
      ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
        * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2)) := hAB.2.1.mul_left _
  calc Work.Diff.STE.CSq s
        (fun m => cLam k m * Work.Diff.STE.conv a c m
          - Work.Diff.STE.conv a (fun m => cLam k m * c m) m)
      = ∑' m : ι → ℤ, (Work.Diff.STE.wt m) ^ s
          * ‖cLam k m * Work.Diff.STE.conv a c m
              - Work.Diff.STE.conv a (fun j => cLam k j * c j) m‖ ^ 2 := rfl
    _ ≤ ∑' m : ι → ℤ, L1 * C1 * ∑' j : ι → ℤ,
          ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
            * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2) :=
        Summable.tsum_le_tsum (fun m => hPoint m) hsumL hsumR
    _ = L1 * C1 * (∑' m : ι → ℤ, ∑' j : ι → ℤ,
          ((Work.Diff.STE.wt (m - j)) ^ (s + 2 * k) * ‖a (m - j)‖)
            * ((Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2)) := tsum_mul_left
    _ = L1 * C1 * ((∑' l : ι → ℤ, (Work.Diff.STE.wt l) ^ (s + 2 * k) * ‖a l‖)
          * (∑' j : ι → ℤ, (Work.Diff.STE.wt j) ^ (s + 2 * k - 1) * ‖c j‖ ^ 2)) := by
        rw [hAB.2.2]
    _ = (L1 * C1 * Lw) * Work.Diff.STE.CSq (s + 2 * k - 1) c := by
        rw [hLwdef]; simp only [Work.Diff.STE.CSq]; ring

end Work.Diff.STE.B3.SymCalcStep1
