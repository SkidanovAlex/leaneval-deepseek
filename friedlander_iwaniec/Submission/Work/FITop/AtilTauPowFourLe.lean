import Mathlib
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.Work.FITop.AdTauAggregate
import Submission.Work.FITop.WolkeSquarefreeTau
import Submission.Work.FITop.AtilTau4Swap
import Submission.Work.FITop.AtilInnerSumLeAd

namespace Work.FITop

open Finset

/-- The `τ⁴`-weighted sum of the squarefree-supported sequence `ã = atilFIa` is
`≪ A(x)(log x)^{2^17}`.  Proof route (all ingredients already in the workspace):
* for `n ∈ Icc 1 x` with `ã n ≠ 0` one has `Squarefree n` (`atil_zero_of_not_squarefree`), so
  `Commons.NumberTheory.Sieve.squarefree_dvd_le_rpow_tau_le n 3` (or the proved
  `Work.FITop.WolkeSquarefreeTau` in `Submission/Work/FITop/WolkeSquarefreeTau.lean`) gives
  `d ∣ n`, `d ^ 3 ≤ n`, `n.divisors.card ≤ (2 * d.divisors.card) ^ 3`, whence
  `τ(n)^4 ≤ (2 τ(d))^12`;
* replace `τ(n)^4` by the sum over the divisors `d` of `n` with `d ^ 3 ≤ n` of `(2τ(d))^12`
  (which dominates it) and swap the two sums: the modulus range becomes `d ^ 3 ≤ x`, i.e.
  `d ≤ ⌊x^{1/3}⌋₊`;
* for `d` squarefree the inner sum is
  `∑_{n : d ∣ n, n ≤ x} ã n ≤ (Submission.Ad d x : ℝ)`, and `τ(d)^12 ≤ τ(d)^15`, so the proved
  `Work.FITop.AdTauAggregate` (`Submission/Work/FITop/AdTauAggregate.lean`) applies with
  `D = ⌊x^{1/3}⌋₊` giving `∑_{d ≤ D, ♭} τ(d)^15 A_d(x) ≤ C · A(x) · (log x)^{2^17}`;
  for `d` non-squarefree the inner sum vanishes (`n` squarefree, `d ∣ n`);
* collect the constants (`2^12` and the `2^17`-th power of `log`).
The conclusion is stated with `Submission.Aseq` (the paper's `A(x)`); `Aseq x ≍ Ã(x)` is not
needed here. -/
theorem AtilTauPowFourLe :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∑ n ∈ Finset.Icc 1 x, atilFIa n * ((n.divisors.card : ℝ)) ^ 4
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (2 ^ 17) := by
  obtain ⟨C0, hC0pos, hAgg⟩ := AdTauAggregate
  refine ⟨max 1 ((2 : ℝ) ^ 12 * C0), lt_of_lt_of_le zero_lt_one (le_max_left _ _), 2, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := hx
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hlognn : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hxR1
  have hAseqnn : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
  set S : Finset ℕ := (Finset.Icc 1 ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊).filter Squarefree with hS
  -- ### Step 1: the `τ⁴`-sum is at most the swapped double sum over squarefree `d ≤ x^{1/3}`
  have hstep1 : (∑ n ∈ Finset.Icc 1 x, atilFIa n * ((n.divisors.card : ℝ)) ^ 4)
      ≤ ∑ d ∈ S, (2 * ((d.divisors.card : ℝ))) ^ 12 *
          (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), atilFIa n) := by
    rw [hS]
    exact AtilTau4Swap x
  -- ### Step 2: the inner `ã`-sums are at most the congruence sums `A_d(x)`
  have hstep2 : (∑ d ∈ S, (2 * ((d.divisors.card : ℝ))) ^ 12 *
        (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), atilFIa n))
      ≤ ∑ d ∈ S, (2 * ((d.divisors.card : ℝ))) ^ 12 * (Submission.Ad d x : ℝ) := by
    refine Finset.sum_le_sum (fun d _ => ?_)
    exact mul_le_mul_of_nonneg_left (AtilInnerSumLeAd d x) (by positivity)
  -- ### Step 3: `(2 τ(d))^{12} ≤ 2^{12} τ(d)^{15}`
  have hstep3 : (∑ d ∈ S, (2 * ((d.divisors.card : ℝ))) ^ 12 * (Submission.Ad d x : ℝ))
      ≤ ∑ d ∈ S, ((2 : ℝ) ^ 12 * ((d.divisors.card : ℝ)) ^ 15) * (Submission.Ad d x : ℝ) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, _⟩, _⟩ := hd
    have hd0 : d ≠ 0 := by omega
    have h1 : (1 : ℝ) ≤ (d.divisors.card : ℝ) := by
      have : 1 ≤ d.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, hd0⟩⟩
      exact_mod_cast this
    have h2 : ((d.divisors.card : ℝ)) ^ 12 ≤ ((d.divisors.card : ℝ)) ^ 15 :=
      pow_le_pow_right₀ h1 (by norm_num)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity))
      (Nat.cast_nonneg _)
  -- ### Step 4: pull out the constant `2^{12}`
  have hstep4 : (∑ d ∈ S, ((2 : ℝ) ^ 12 * ((d.divisors.card : ℝ)) ^ 15) * (Submission.Ad d x : ℝ))
      = (2 : ℝ) ^ 12 * ∑ d ∈ S, ((d.divisors.card : ℝ)) ^ 15 * (Submission.Ad d x : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  -- ### Step 5: the `τ¹⁵`-weighted aggregate `AdTauAggregate`
  have hstep5 : (∑ d ∈ S, ((d.divisors.card : ℝ)) ^ 15 * (Submission.Ad d x : ℝ))
      ≤ C0 * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ ((2 : ℝ) ^ (17 : ℕ)) := by
    rw [hS]
    exact hAgg x ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ hx2 le_rfl
  -- ### Step 6: `(log x)^{2^{17}}` as a natural power
  have hlogpow : (Real.log (x : ℝ)) ^ ((2 : ℝ) ^ (17 : ℕ)) = (Real.log (x : ℝ)) ^ (2 ^ 17) := by
    rw [show ((2 : ℝ) ^ (17 : ℕ)) = ((131072 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hLnn : (0 : ℝ) ≤ (Real.log (x : ℝ)) ^ ((2 : ℝ) ^ (17 : ℕ)) := Real.rpow_nonneg hlognn _
  calc ∑ n ∈ Finset.Icc 1 x, atilFIa n * ((n.divisors.card : ℝ)) ^ 4
      ≤ ∑ d ∈ S, (2 * ((d.divisors.card : ℝ))) ^ 12 *
          (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), atilFIa n) := hstep1
    _ ≤ ∑ d ∈ S, (2 * ((d.divisors.card : ℝ))) ^ 12 * (Submission.Ad d x : ℝ) := hstep2
    _ ≤ ∑ d ∈ S, ((2 : ℝ) ^ 12 * ((d.divisors.card : ℝ)) ^ 15) * (Submission.Ad d x : ℝ) := hstep3
    _ = (2 : ℝ) ^ 12 * ∑ d ∈ S, ((d.divisors.card : ℝ)) ^ 15 * (Submission.Ad d x : ℝ) := hstep4
    _ ≤ (2 : ℝ) ^ 12 *
          (C0 * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ ((2 : ℝ) ^ (17 : ℕ))) :=
        mul_le_mul_of_nonneg_left hstep5 (by positivity)
    _ = ((2 : ℝ) ^ 12 * C0) * (Submission.Aseq x : ℝ) *
          (Real.log (x : ℝ)) ^ ((2 : ℝ) ^ (17 : ℕ)) := by ring
    _ ≤ max 1 ((2 : ℝ) ^ 12 * C0) * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (2 ^ 17) := by
        rw [← hlogpow]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hAseqnn) hLnn

end Work.FITop
