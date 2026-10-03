/-
# `Work.FITop.AdTauAggregate` — the `τ¹⁵`-weighted aggregate of the congruence sums

The companion-sieve/`(2.1)`-type aggregate for the Friedlander–Iwaniec sequence
`a_n = #{(a,c) ∈ ℤ² : a² + c⁴ = n}` in the range the chain needs it:

  `∑_{d ≤ D, ♭} τ(d)^15 · A_d(x) ≤ C · A(x) · (log x)^{2^17}`   for `D ≤ ⌊x^{1/3}⌋`.

The proof is the elementary one: the pointwise bound `A_d(x) ≤ C τ(d)² A(x)/d` for **cubefree**
`d` with `d² ≤ x` (`Submission.ASP.Ad_le_tau_sq_div_of_cubefree`, which is the paper's
replacement of the false companion hypothesis `(1.6)`), together with the divisor-sum estimate
`∑_{d ≤ y} τ(d)^{17}/d ≪ (log y)^{2^17}` (`Commons.NumberTheory.Divisors.sum_tau_pow_div_le`).
The exponent `15 = 17 - 2` is exactly the one that absorbs the `τ(d)²` of the pointwise bound,
and `D ≤ x^{1/3}` gives `d² ≤ d³ ≤ x` so that the pointwise bound applies for every `d ≤ D`.
-/
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
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
-- `Submission.ASP.Ad_le_tau_sq_div_of_cubefree` (the pointwise bound `A_d(x) ≤ C τ(d)²A(x)/d`)
-- lives in `Submission.ASP.S20`, already in the closure of `Windows`; the divisor-sum estimate
-- `∑_{d ≤ y} τ(d)^k/d ≪ (log y)^{2^k}` is `Commons.NumberTheory.Divisors.sum_tau_pow_div_le`.

namespace Work.FITop

open Finset

set_option maxHeartbeats 1600000

/-- **The `τ¹⁵`-weighted aggregate of the congruence sums** `A_d(x)`, `d ≤ D ≤ x^{1/3}`
squarefree.  This is the aggregate form of the paper's §3 estimate that the chain of
`Submission/Work/FITop/Top.lean` consumes. -/
theorem AdTauAggregate :
    ∃ C : ℝ, 0 < C ∧ ∀ x D : ℕ, 2 ≤ x → D ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ →
      (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ (15 : ℕ) * (Submission.Ad d x : ℝ))
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ ((2 : ℝ) ^ (17 : ℕ)) := by
  obtain ⟨C0, hC0pos, hAd⟩ := Submission.ASP.Ad_le_tau_sq_div_of_cubefree
  obtain ⟨C1, hC1pos, hSum⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 17
  refine ⟨max 1 (C0 * C1 * (2 : ℝ) ^ (131072 : ℕ)),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x D hx hD
  have hx1 : 1 ≤ x := by omega
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hA0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
  have hfloorle : ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
    Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hDcast : (D : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
    le_trans (by exact_mod_cast hD) hfloorle
  have hDx : D ≤ x := by
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (x : ℝ) := by
      have h3 := Real.rpow_le_rpow_of_exponent_le hxR1 (by norm_num : ((1 : ℝ) / 3) ≤ (1 : ℝ))
      rwa [Real.rpow_one] at h3
    exact_mod_cast le_trans hDcast h2
  -- the pointwise bound, termwise
  have hterm : ∀ d ∈ (Finset.Icc 1 D).filter Squarefree,
      ((d.divisors.card : ℝ)) ^ (15 : ℕ) * (Submission.Ad d x : ℝ)
        ≤ C0 * (Submission.Aseq x : ℝ) * (((d.divisors.card : ℝ)) ^ (17 : ℕ) / (d : ℝ)) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdD⟩, hdsq⟩ := hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have hdcast : (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
      le_trans (by exact_mod_cast (le_trans hdD hD)) hfloorle
    have hcube : (d : ℝ) ^ 3 ≤ (x : ℝ) := by
      have h1 : ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (x : ℝ) := by
        rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 3)) 3,
            ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (x : ℝ)),
            show ((1 : ℝ) / 3) * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
      calc (d : ℝ) ^ 3 ≤ ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 :=
            pow_le_pow_left₀ (le_of_lt hd0R) hdcast 3
        _ = (x : ℝ) := h1
    have hdx : d ^ 2 ≤ x := by
      have h2 : (d : ℝ) ^ 2 ≤ (x : ℝ) := by
        have h4 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 3 := pow_le_pow_right₀ hd1R (by norm_num : 2 ≤ 3)
        linarith
      exact_mod_cast h2
    have hcb : ∀ p : ℕ, Nat.Prime p → ¬ p ^ 3 ∣ d := by
      intro p hp hp3
      refine (Nat.squarefree_iff_prime_squarefree.mp hdsq p hp) ?_
      have hpp : p * p ∣ p ^ 3 := by
        rw [show p ^ 3 = (p * p) * p by ring]
        exact dvd_mul_right _ _
      exact dvd_trans hpp hp3
    calc ((d.divisors.card : ℝ)) ^ (15 : ℕ) * (Submission.Ad d x : ℝ)
        ≤ ((d.divisors.card : ℝ)) ^ (15 : ℕ) *
            (C0 * (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ)) * (Submission.Aseq x : ℝ)) :=
          mul_le_mul_of_nonneg_left (hAd d x hd1 hcb hdx) (by positivity)
      _ = C0 * (Submission.Aseq x : ℝ) * (((d.divisors.card : ℝ)) ^ (17 : ℕ) / (d : ℝ)) := by
          ring_nf
  have hmain1 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ (15 : ℕ) * (Submission.Ad d x : ℝ))
      ≤ C0 * (Submission.Aseq x : ℝ) *
        (∑ d ∈ Finset.Icc 1 (max D 1), ((d.divisors.card : ℝ)) ^ (17 : ℕ) / (d : ℝ)) := by
    calc (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            ((d.divisors.card : ℝ)) ^ (15 : ℕ) * (Submission.Ad d x : ℝ))
        ≤ ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            C0 * (Submission.Aseq x : ℝ) * (((d.divisors.card : ℝ)) ^ (17 : ℕ) / (d : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = C0 * (Submission.Aseq x : ℝ) * ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            (((d.divisors.card : ℝ)) ^ (17 : ℕ) / (d : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ C0 * (Submission.Aseq x : ℝ) * ∑ d ∈ Finset.Icc 1 (max D 1),
            (((d.divisors.card : ℝ)) ^ (17 : ℕ) / (d : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0pos.le hA0)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            rw [Finset.mem_filter, Finset.mem_Icc] at hd
            rw [Finset.mem_Icc]
            exact ⟨hd.1.1, le_trans hd.1.2 (le_max_left _ _)⟩
          · intro d _ _
            positivity
  have hmain2 : (∑ d ∈ Finset.Icc 1 (max D 1), ((d.divisors.card : ℝ)) ^ (17 : ℕ) / (d : ℝ))
      ≤ C1 * (Real.log (((max D 1 : ℕ) : ℝ) + 2)) ^ (131072 : ℕ) := by
    have h := hSum (max D 1) (le_max_right D 1)
    have h2 : (2 : ℕ) ^ 17 = 131072 := by norm_num
    rwa [h2] at h
  have hmaxx : max D 1 ≤ x := max_le hDx hx1
  have hlogpow : (Real.log (((max D 1 : ℕ) : ℝ) + 2)) ^ (131072 : ℕ)
      ≤ (2 : ℝ) ^ (131072 : ℕ) * (Real.log (x : ℝ)) ^ (131072 : ℕ) := by
    have h1 : ((max D 1 : ℕ) : ℝ) + 2 ≤ 2 * (x : ℝ) := by
      have h2 : ((max D 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hmaxx
      linarith
    have h2 : Real.log (((max D 1 : ℕ) : ℝ) + 2) ≤ 2 * Real.log (x : ℝ) := by
      have hpos : (0 : ℝ) < ((max D 1 : ℕ) : ℝ) + 2 := by positivity
      have h5 : Real.log (((max D 1 : ℕ) : ℝ) + 2) ≤ Real.log (2 * (x : ℝ)) :=
        Real.log_le_log hpos h1
      have h6 : Real.log (2 * (x : ℝ)) = Real.log 2 + Real.log (x : ℝ) :=
        Real.log_mul (by norm_num) (by positivity)
      have h7 : Real.log 2 ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) hxR2
      linarith
    have h3 : 0 ≤ Real.log (((max D 1 : ℕ) : ℝ) + 2) := by
      apply Real.log_nonneg
      have h4 : (1 : ℝ) ≤ ((max D 1 : ℕ) : ℝ) := by exact_mod_cast (le_max_right D 1)
      linarith
    calc (Real.log (((max D 1 : ℕ) : ℝ) + 2)) ^ (131072 : ℕ)
        ≤ (2 * Real.log (x : ℝ)) ^ (131072 : ℕ) := pow_le_pow_left₀ h3 h2 _
      _ = (2 : ℝ) ^ (131072 : ℕ) * (Real.log (x : ℝ)) ^ (131072 : ℕ) := mul_pow _ _ _
  have hconv : (Real.log (x : ℝ)) ^ (131072 : ℕ) = (Real.log (x : ℝ)) ^ ((2 : ℝ) ^ (17 : ℕ)) := by
    rw [show ((2 : ℝ) ^ (17 : ℕ)) = ((131072 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ (15 : ℕ) * (Submission.Ad d x : ℝ))
      ≤ C0 * (Submission.Aseq x : ℝ) *
          (∑ d ∈ Finset.Icc 1 (max D 1), ((d.divisors.card : ℝ)) ^ (17 : ℕ) / (d : ℝ)) := hmain1
    _ ≤ C0 * (Submission.Aseq x : ℝ) *
          (C1 * (Real.log (((max D 1 : ℕ) : ℝ) + 2)) ^ (131072 : ℕ)) :=
        mul_le_mul_of_nonneg_left hmain2 (mul_nonneg hC0pos.le hA0)
    _ ≤ C0 * (Submission.Aseq x : ℝ) *
          (C1 * ((2 : ℝ) ^ (131072 : ℕ) * (Real.log (x : ℝ)) ^ (131072 : ℕ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogpow hC1pos.le)
          (mul_nonneg hC0pos.le hA0)
    _ = C0 * C1 * (2 : ℝ) ^ (131072 : ℕ) * (Submission.Aseq x : ℝ) *
          (Real.log (x : ℝ)) ^ ((2 : ℝ) ^ (17 : ℕ)) := by rw [hconv]; ring
    _ ≤ max 1 (C0 * C1 * (2 : ℝ) ^ (131072 : ℕ)) * (Submission.Aseq x : ℝ) *
          (Real.log (x : ℝ)) ^ ((2 : ℝ) ^ (17 : ℕ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0)
          (Real.rpow_nonneg hlogx_pos.le _)

end Work.FITop
