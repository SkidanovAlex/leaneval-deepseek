import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Shared vocabulary for the Richert/Ford growth bound `Work.BMF.zeta_growth_strip`. -/

namespace Work.BMF

open Complex

/-- The **Vinogradov–Korobov exponential-sum bound** (Ford, *Vinogradov's integral and bounds
for the Riemann zeta function*, Theorem 2). -/
def VKExpSum (C D : ℝ) : Prop :=
  ∀ (N t : ℝ), 2 ≤ N → N ≤ t → ∀ u : ℝ, 0 < u → u ≤ 1 →
    ∀ R : ℝ, N < R → R ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
        C * N ^ (1 - 1 / (D * (Real.log t / Real.log N) ^ 2))

/-- **Euler–Maclaurin bound.**  For `σ > 0`, `|t| ≥ 1`, `N ≥ 1`,
`‖ζ(σ+it)‖ ≤ Σ_{n≤N} n^{-σ} + N^{1-σ}/|t| + (‖σ+it‖/σ) N^{-σ}`. -/
lemma zeta_emN_bound {σ t : ℝ} (hσ0 : 0 < σ) (ht : 1 ≤ |t|) (N : ℕ) (hN : 1 ≤ N) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ))
        + (((N : ℕ) : ℝ) ^ (1 - σ)) / |t|
        + (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * ((N : ℕ) : ℝ) ^ (-σ) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hs0 : 0 < s.re := by rw [hsre]; exact hσ0
  have hs1 : s ≠ 1 := by
    intro h
    have hsi : s.im = 0 := by simpa using congrArg Complex.im h
    have : t = 0 := by simpa [hsim] using hsi
    have habs : |t| = 0 := by rw [this]; simp
    have : (0:ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
    linarith
  have hid := Commons.NumberTheory.Zeta.zeta_eq_emN (s := s) hs0 hs1 N hN
  have hH : ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ) := by
    calc ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖(((n : ℕ) : ℂ) ^ (-s))‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hcast : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by norm_num
        rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-s), Complex.neg_re, hsre]
  have hM : ‖((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖ ≤ (((N : ℕ) : ℝ) ^ (1 - σ)) / |t| := by
    have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hnum : ‖(((N : ℕ) : ℂ) ^ (1 - s))‖ = ((N : ℕ) : ℝ) ^ (1 - σ) := by
      have hcast : ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) := by norm_num
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hN0 (1 - s), Complex.sub_re,
        Complex.one_re, hsre]
    have hden : |t| ≤ ‖s - 1‖ := by
      have h1 : |(s - 1).im| ≤ ‖s - 1‖ := abs_im_le_norm (s - 1)
      have h2 : (s - 1).im = t := by simp [hsim]
      rwa [h2] at h1
    have hpos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
    rw [norm_div, hnum]
    exact div_le_div_of_nonneg_left (by positivity) hpos hden
  obtain ⟨hsum, hbd⟩ := Commons.NumberTheory.Zeta.emTerm_tsum_le N hN s hs0 hs1
  have hT' : ‖(∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖
      ≤ (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re) :=
    le_trans (norm_tsum_le_tsum_norm hsum.norm) (by simpa using hbd)
  rw [hid]
  have htri : ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
        ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) +
        (∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖
        + ‖((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖
        + ‖(∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖ := by
    have h1 := norm_add_le ((∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
        ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)))
      (∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))
    have h2 := norm_add_le (∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))
      ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))
    linarith
  calc _ ≤ _ := htri
    _ ≤ _ + _ + _ := add_le_add (add_le_add hH hM) hT'
    _ = (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ))
        + (((N : ℕ) : ℝ) ^ (1 - σ)) / |t|
        + (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * ((N : ℕ) : ℝ) ^ (-σ) := by
        rw [hs]; simp [hsre]

end Work.BMF
