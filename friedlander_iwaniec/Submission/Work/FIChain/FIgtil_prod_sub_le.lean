import Mathlib
import Submission.Work.FIChain.Defs

namespace Work.FIChain

open Finset

/-- The modified density `g̃` never exceeds `1`: on squarefree `d` it is the product of the
prime factors `g̃(p) ∈ [0,1)`, and it vanishes on non-squarefree `d`. -/
private lemma FIgtil_le_one (d : ℕ) : Submission.ASP.FIgtil d ≤ 1 := by
  rw [Submission.ASP.FIgtil]
  by_cases h : Squarefree d
  · rw [if_pos h]
    refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => le_of_lt ?_)
    · obtain ⟨hp1, -, -⟩ := Nat.mem_primeFactors.mp hp
      exact Submission.ASP.gtilVal_nonneg (Submission.ASP.FIg_nonneg _)
        (Submission.ASP.FI_gdens_prime_sq_le p hp1).1 (Submission.ASP.FI_gdens_prime_nonneg hp1).2
    · obtain ⟨hp1, -, -⟩ := Nat.mem_primeFactors.mp hp
      exact Submission.ASP.gtilVal_lt_one (Submission.ASP.FI_gdens_prime_nonneg hp1).2
        (by have h2 := Submission.ASP.FIg_prime_sq_le_half hp1; linarith)
  · rw [if_neg h]; norm_num

/-- The partial Euler product `∏_{p < Δ} (1 - g̃(p))` is `O(1/log Δ)`.

The sum `∑_{p ≤ Δ} g̃(p) = log log Δ + O(1)` (that is `ASP.S27.FIgtil_sum_19_nat`), and each
factor satisfies `1 - g̃(p) ≤ exp(-g̃(p))`, so

  `∏_{p < Δ} (1 - g̃(p)) ≤ exp(-∑_{p < Δ} g̃(p)) = O(1/log Δ)`.

The passage from the sum over `p ≤ Δ` to the sum over `p < Δ` costs at most one factor, since
`g̃(d) ≤ 1` for every `d`. -/
theorem FIgtil_prod_sub_le :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ Δ : ℕ, 3 ≤ Δ →
      ∏ p ∈ Nat.primesBelow Δ, (1 - Submission.ASP.FIgtil p) ≤ C₁ / Real.log (Δ : ℝ) := by
  obtain ⟨c, C, h19⟩ := Submission.ASP.FIgtil_sum_19_nat
  refine ⟨Real.exp (1 + |C| * (4/3) - c), Real.exp_pos _, fun Δ hΔ => ?_⟩
  have hΔ1 : 1 < Δ := by omega
  have hR1 : (1:ℝ) < (Δ:ℝ) := by exact_mod_cast hΔ1
  have hLpos : 0 < Real.log (Δ:ℝ) := Real.log_pos hR1
  have hL1 : 1 ≤ Real.log (Δ:ℝ) := by
    have h3 : 1 < Real.log (3:ℝ) := (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
    have hle : Real.log (3:ℝ) ≤ Real.log (Δ:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hΔ)
    linarith
  -- the error term of (1.9) is bounded by `4/3` for every `Δ ≥ 3`
  have hE : (Real.log (Δ:ℝ)) ^ (-(10:ℝ)) + 1 / (Δ:ℝ) ≤ 4/3 := by
    have h1 : (Real.log (Δ:ℝ)) ^ (-(10:ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
    have h2 : 1 / (Δ:ℝ) ≤ 1/3 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hΔ)
    linarith
  have hΔ2 : 2 ≤ Δ := by omega
  have h19Δ := h19 Δ hΔ2
  have hE0 : 0 ≤ (Real.log (Δ:ℝ)) ^ (-(10:ℝ)) + 1 / (Δ:ℝ) := by
    have := Real.rpow_nonneg hLpos.le (-(10:ℝ)); positivity
  -- the primes `≤ Δ` are the primes `< Δ` together with `Δ` itself
  have hBA : (Finset.Icc 1 Δ).filter Nat.Prime ⊆ insert Δ (Nat.primesBelow Δ) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hp2⟩, hpp⟩ := hp
    rcases eq_or_lt_of_le hp2 with rfl | hlt
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Nat.mem_primesBelow.mpr ⟨hlt, hpp⟩)
  have hsum_le : (∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, Submission.ASP.FIgtil p)
      ≤ (∑ p ∈ Nat.primesBelow Δ, Submission.ASP.FIgtil p) + 1 := by
    have h1 : (∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, Submission.ASP.FIgtil p)
        ≤ ∑ p ∈ insert Δ (Nat.primesBelow Δ), Submission.ASP.FIgtil p :=
      Finset.sum_le_sum_of_subset_of_nonneg hBA (fun i _ _ => Submission.ASP.FIgtil_nonneg i)
    have h2 : (∑ p ∈ insert Δ (Nat.primesBelow Δ), Submission.ASP.FIgtil p)
        = Submission.ASP.FIgtil Δ + ∑ p ∈ Nat.primesBelow Δ, Submission.ASP.FIgtil p := by
      rw [Finset.sum_insert]
      intro hmem
      exact absurd (Nat.mem_primesBelow.mp hmem).1 (lt_irrefl Δ)
    have h3 : Submission.ASP.FIgtil Δ ≤ 1 := FIgtil_le_one Δ
    linarith
  have hbound : -(|C| * ((Real.log (Δ:ℝ)) ^ (-(10:ℝ)) + 1 / (Δ:ℝ)))
      ≤ (∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, Submission.ASP.FIgtil p)
        - Real.log (Real.log (Δ:ℝ)) - c := by
    have h1 := neg_le_of_abs_le h19Δ
    have h2 : C * ((Real.log (Δ:ℝ)) ^ (-(10:ℝ)) + 1 / (Δ:ℝ))
        ≤ |C| * ((Real.log (Δ:ℝ)) ^ (-(10:ℝ)) + 1 / (Δ:ℝ)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hE0
    linarith
  have hSA : Real.log (Real.log (Δ:ℝ)) + c - |C| * (4/3) - 1
      ≤ ∑ p ∈ Nat.primesBelow Δ, Submission.ASP.FIgtil p := by
    have h4 : |C| * ((Real.log (Δ:ℝ)) ^ (-(10:ℝ)) + 1 / (Δ:ℝ)) ≤ |C| * (4/3) :=
      mul_le_mul_of_nonneg_left hE (abs_nonneg C)
    linarith
  -- `1 - x ≤ exp(-x)` for every real `x`
  have hprod : (∏ p ∈ Nat.primesBelow Δ, (1 - Submission.ASP.FIgtil p))
      ≤ Real.exp (-(∑ p ∈ Nat.primesBelow Δ, Submission.ASP.FIgtil p)) := by
    have h1 : (∏ p ∈ Nat.primesBelow Δ, (1 - Submission.ASP.FIgtil p))
        ≤ ∏ p ∈ Nat.primesBelow Δ, Real.exp (-(Submission.ASP.FIgtil p)) := by
      refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
      · have hpp := (Nat.mem_primesBelow.mp hp).2
        have := Submission.ASP.FIgtil_lt_one hpp
        linarith
      · exact Real.one_sub_le_exp_neg (Submission.ASP.FIgtil p)
    have h2 : (∏ p ∈ Nat.primesBelow Δ, Real.exp (-(Submission.ASP.FIgtil p)))
        = Real.exp (-(∑ p ∈ Nat.primesBelow Δ, Submission.ASP.FIgtil p)) := by
      rw [(Real.exp_sum (Nat.primesBelow Δ) (fun p => -(Submission.ASP.FIgtil p))).symm,
        Finset.sum_neg_distrib]
    linarith
  have hexp : Real.exp (-(∑ p ∈ Nat.primesBelow Δ, Submission.ASP.FIgtil p))
      ≤ Real.exp (-(Real.log (Real.log (Δ:ℝ)) + c - |C| * (4/3) - 1)) :=
    Real.exp_le_exp.mpr (by linarith)
  calc (∏ p ∈ Nat.primesBelow Δ, (1 - Submission.ASP.FIgtil p))
      ≤ Real.exp (-(∑ p ∈ Nat.primesBelow Δ, Submission.ASP.FIgtil p)) := hprod
    _ ≤ Real.exp (-(Real.log (Real.log (Δ:ℝ)) + c - |C| * (4/3) - 1)) := hexp
    _ = Real.exp (1 + |C| * (4/3) - c) / Real.log (Δ:ℝ) := by
        rw [show -(Real.log (Real.log (Δ:ℝ)) + c - |C| * (4/3) - 1)
            = -Real.log (Real.log (Δ:ℝ)) + (1 + |C| * (4/3) - c) by ring,
            Real.exp_add, Real.exp_neg, Real.exp_log hLpos]
        ring

end Work.FIChain
