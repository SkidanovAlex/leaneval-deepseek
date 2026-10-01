import Mathlib
import Submission.Work.LinnikAreas.CIDeps
import Submission.Work.NumberTheory.Linnik.leastPrimeBound

/-!
# `UniformPrimePowerTail`

The contribution of the *non-prime* terms (`n = p ^ k`, `k ≥ 2`, i.e. the
exponent-`≥ 2` prime powers) to the class-filtered, tent-weighted von Mangoldt
sum is `O(q ^ (-(49/20)))`, uniformly in the truncation `X` and in the residue
class `a`.

This is the `L = 11 / 2`, `K = 3 / 10` instance of
`Commons.NumberTheory.Linnik.nonprime_class_bound`, but with the (implicit)
constant of that statement *made explicit and uniform in `q`*: the underlying
constant is `(3/10) * (3 * B)` where `B` is the absolute constant of the
Chebyshev prime-power estimate `ψ - θ = O(√x)`.  Concretely the tent weight
`tentWeight L K` vanishes below `q ^ (L - 2K)`, and Abel summation against
`∑_{n ≤ m, n = p^k, k ≥ 2} Λ n = O(√m)` gives the tail bound
`∑ Λ(n)/n ≤ 3B / √(q ^ (L - 2K))`; with `L - 2K = 11/2 - 6/10 = 49/10` this is
`3B * q ^ (-(49/20))`.
-/

open scoped BigOperators
open Finset

namespace Work.LinnikAreas

/-- **Uniform (§13) prime-power tail estimate.**  Fix `L, K` with `2 ≤ L - 2K`
and an *absolute* cumulative bound `B` for the exponent-`≥ 2` prime powers
(`∑_{k ≤ m} ppLambda k ≤ B √m`).  Then for every modulus `q ≥ 2` and every
truncation `X`, the `Λ(n)/n`-weighted tail above the threshold `q ^ (L - 2K)`
is at most `3B / √(q ^ (L - 2K))`.

The point of the statement (vis-à-vis `nonprime_tail_le`) is that the constant
`B` is a *parameter*, so the bound is manifestly uniform in `q`. -/
private lemma nonprime_tail_le_fixed {L K B : ℝ} (hBpos : 0 < B)
    (hBbd : ∀ x : ℝ, 0 ≤ x →
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Commons.NumberTheory.Linnik.ppLambda n)
        ≤ B * Real.sqrt x)
    (hLK : 2 ≤ L - 2 * K) :
    ∀ q : ℕ, 2 ≤ q → ∀ X : ℕ,
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
            ¬ n.Prime ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          ArithmeticFunction.vonMangoldt n / (n : ℝ))
        ≤ 3 * B / Real.sqrt ((q : ℝ) ^ (L - 2 * K)) := by
  intro q hq X
  classical
  set T : ℝ := (q : ℝ) ^ (L - 2 * K) with hT
  set N : ℕ := Nat.ceil T with hN
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hT4 : (2 : ℝ) ≤ T := by
    have h1 : ((2 : ℝ) ^ (2 : ℝ)) ≤ T := by
      rw [hT]
      calc ((2 : ℝ) ^ (2 : ℝ)) ≤ (2 : ℝ) ^ (L - 2 * K) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hLK
        _ ≤ (q : ℝ) ^ (L - 2 * K) :=
            Real.rpow_le_rpow (by norm_num) hq2 (le_trans zero_le_two hLK)
    have h2 : ((2 : ℝ) ^ (2 : ℝ)) = 4 := by rw [Real.rpow_two]; norm_num
    rw [h2] at h1
    linarith
  have hN2 : 2 ≤ N := by
    have h := Nat.ceil_mono hT4
    rw [hN]
    have : Nat.ceil (2 : ℝ) = 2 := by simp
    omega
  have hcum : ∀ m : ℕ,
      (∑ k ∈ Finset.Icc 0 m, Commons.NumberTheory.Linnik.ppLambda k) ≤ B * Real.sqrt (m : ℝ) :=
    Commons.NumberTheory.Linnik.ppLambda_cum_bound (fun x hx => hBbd x hx)
  have hstep1a : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ T ≤ (n : ℝ)),
          ArithmeticFunction.vonMangoldt n / (n : ℝ))
      ≤ (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ T ≤ (n : ℝ)),
          Commons.NumberTheory.Linnik.ppLambda n / (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    exact div_le_div_of_nonneg_right (Commons.NumberTheory.Linnik.le_ppLambda hn.2.1)
      (by positivity)
  have hstep1b : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ T ≤ (n : ℝ)),
          Commons.NumberTheory.Linnik.ppLambda n / (n : ℝ))
      ≤ (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => N ≤ n),
          Commons.NumberTheory.Linnik.ppLambda n / (n : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨hn.1, Nat.ceil_le.mpr hn.2.2⟩
    · intro n hn _
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      exact div_nonneg (Commons.NumberTheory.Linnik.ppLambda_nonneg n) (by positivity)
  have hstep1 := le_trans hstep1a hstep1b
  have hstep2 : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => N ≤ n),
          Commons.NumberTheory.Linnik.ppLambda n / (n : ℝ))
      ≤ (∑ n ∈ Finset.Icc N X, Commons.NumberTheory.Linnik.ppLambda n / (n : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨hn.2, hn.1.2⟩
    · intro n hn _
      simp only [Finset.mem_Icc] at hn
      exact div_nonneg (Commons.NumberTheory.Linnik.ppLambda_nonneg n) (by positivity)
  have hstep3 : (∑ n ∈ Finset.Icc N X, Commons.NumberTheory.Linnik.ppLambda n / (n : ℝ))
      ≤ 3 * B / Real.sqrt (N : ℝ) := by
    by_cases hNX : N ≤ X
    · exact Commons.Analysis.InfiniteSum.partialDivSumLeOfCumulativeSqrt
        Commons.NumberTheory.Linnik.ppLambda_nonneg (le_of_lt hBpos) hcum hN2 hNX
    · rw [Finset.Icc_eq_empty hNX, Finset.sum_empty]
      positivity
  have hle : (N : ℝ) ≥ T := Nat.le_ceil T
  have hsqrt : Real.sqrt T ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hle
  have hTpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  have hfinal : 3 * B / Real.sqrt (N : ℝ) ≤ 3 * B / Real.sqrt T :=
    div_le_div_of_nonneg_left (by linarith [hBpos]) hTpos hsqrt
  refine le_trans ?_ hfinal
  exact le_trans (le_trans hstep1 hstep2) hstep3

theorem UniformPrimePowerTail :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ a X : ℕ,
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
          ArithmeticFunction.vonMangoldt n / (n : ℝ) *
            Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
              (Real.log (n : ℝ) / Real.log (q : ℝ)))
        ≤ C * (q : ℝ) ^ (-(49/20 : ℝ)) := by
  obtain ⟨B, hBpos, hBbd⟩ := Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt
  refine ⟨(3 / 10) * (3 * B), by nlinarith [hBpos], ?_⟩
  intro q hq a X
  have hK : (0 : ℝ) < 3 / 10 := by norm_num
  have hLK : (2 : ℝ) ≤ (11 / 2 : ℝ) - 2 * (3 / 10) := by norm_num
  have h2K : 2 * (3 / 10 : ℝ) < (11 / 2 : ℝ) := by norm_num
  have hsum_eq : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
        ArithmeticFunction.vonMangoldt n / (n : ℝ) *
          Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
            (Real.log (n : ℝ) / Real.log (q : ℝ)))
      = (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
            ((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
              (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hw : 0 ≤ Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
        (Real.log (n : ℝ) / Real.log (q : ℝ)) :=
      (Commons.NumberTheory.Linnik.tentWeight_bounds (by norm_num) (by norm_num)).1 _
    rw [norm_mul, Complex.norm_div,
        show ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ =
            ArithmeticFunction.vonMangoldt n from by
          rw [Complex.norm_real]; exact Real.norm_of_nonneg hΛ,
        show ‖(n : ℂ)‖ = (n : ℝ) from Complex.norm_natCast n,
        show ‖(((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
            (Real.log (n : ℝ) / Real.log (q : ℝ))) : ℝ) : ℂ)‖ =
          Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
            (Real.log (n : ℝ) / Real.log (q : ℝ)) from by
          rw [Complex.norm_real]; exact Real.norm_of_nonneg hw]
  rw [hsum_eq]
  have hdrop := Commons.NumberTheory.Linnik.nonprime_sum_drop_below (q := q) (X := X) (a := a)
      (L := (11/2 : ℝ)) (K := (3/10 : ℝ)) (by positivity) (le_of_lt h2K) hq
  have hres := Commons.NumberTheory.Linnik.nonprime_restricted_le' (q := q) (X := X) (a := a)
      (L := (11/2 : ℝ)) (K := (3/10 : ℝ)) hK h2K hq
  have htail := nonprime_tail_le_fixed (L := (11/2 : ℝ)) (K := (3/10 : ℝ))
      (B := B) hBpos hBbd hLK q hq X
  have hmain : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
            ((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
              (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖)
      ≤ (3 / 10) * (3 * B / Real.sqrt ((q : ℝ) ^ ((11 / 2 : ℝ) - 2 * (3 / 10)))) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left htail (by norm_num))
    rw [hdrop]
    exact hres
  refine le_trans hmain ?_
  have hexp : (11 / 2 : ℝ) - 2 * (3 / 10) = (49 / 10 : ℝ) := by norm_num
  rw [hexp]
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hsqrt : Real.sqrt ((q : ℝ) ^ (49 / 10 : ℝ)) = (q : ℝ) ^ (49 / 20 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hqpos.le,
        show (49 / 10 : ℝ) * (1 / 2) = 49 / 20 from by norm_num]
  have hsingle : (3 : ℝ) * B / (q : ℝ) ^ (49 / 20 : ℝ) = (3 * B) * (q : ℝ) ^ (-(49 / 20 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hqpos.le]
  rw [hsqrt, hsingle]
  exact le_of_eq (by ring)

end Work.LinnikAreas
