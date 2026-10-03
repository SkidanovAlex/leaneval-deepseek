/-
# `Submission.Work.FIFinal.Endgame` — from the chain's prime-sum bound to the challenge

This module closes the *last mile*: given the prime-sum asymptotic of the chain
(`Work.FIFinal.PrimeSumBound`, the target of `Work.FIChain.primeSum_bound_of_prop41'` and the
statement of the single `sorry` of `Submission/Work/FITop/Top.lean`),

  `|Σ_{p ≤ N} (log p)·a_p − (4/π)·A(N)| ≤ C·Ã(N)·loglog N/log N`  eventually in `N`,

it derives the challenge theorem `{p : ℕ | p.Prime ∧ ∃ a b, p = a² + b⁴}.Infinite`.

The argument is the one proved in `Submission/Work/FITop/Top.lean` §4–§5, reproduced here because
that module is not importable (it carries the `sorry`ed leaf `Work.FITop.primeSum_bound_of_prop41`,
and importing it would put `sorryAx` in scope of this chapter's `#print axioms`).  Nothing here is
new mathematics: the numerical margin `4κ/π > 1.11`
(`Submission.one_lt_four_pi_kappa`), the classical pair count
`card_sq_add_pow_four_intpairs_asymptotic`, the elementary absorption `Work.FITop.absorption`, the
margin arithmetic `Work.FITop.MarginArith`, and the identity `primeSum = (1/4)·Σ_{p≤N} log p·a_p`
(`Submission.ASP.primeSum_eq_quarter`).  The only input beyond those is `PrimeSumBound` itself.
-/
import Mathlib
import Submission.Work.FIFinal.Defs
import Submission.Work.FITop.MarginArith
import Submission.Work.FITop.Defs
import Submission.ASP.S27
import Submission.Final
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_intpairs_ncard
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_intpairs_asymptotic

set_option autoImplicit false

namespace Work.FIFinal

open Finset Filter
open scoped BigOperators

noncomputable section

/-- `Ã(N) ≤ A(N) ≤ Aseq N` (`Acount FIa N = Aseq N − 1`). -/
lemma AcountTil_le_Aseq (N : ℕ) : AcountTil N ≤ (Submission.Aseq N : ℝ) := by
  have h1 : AcountTil N ≤ AcountF N := by
    rw [AcountTil, AcountF, Submission.ASP.Acount, Submission.ASP.Acount]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [Work.FITop.atilFIa, Submission.ASP.atil]
    have hnn : 0 ≤ Submission.ASP.FIa n := by
      rw [Submission.ASP.FIa]; exact_mod_cast Nat.zero_le _
    have hmu : ((ArithmeticFunction.moebius n : ℝ)) ^ 2 ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := n)
      have h2 : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by exact_mod_cast h
      nlinarith [abs_nonneg (ArithmeticFunction.moebius n : ℝ),
        sq_abs (ArithmeticFunction.moebius n : ℝ)]
    nlinarith [mul_le_mul_of_nonneg_right hmu hnn]
  refine le_trans h1 ?_
  have h2 : AcountF N = (Submission.Aseq N : ℝ) - 1 := by
    rw [AcountF, Submission.ASP.FI_Acount_eq]
  have h3 : (1 : ℝ) ≤ (Submission.Aseq N : ℝ) := by
    have hmem : 0 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.succ_pos N)
    have hle : Submission.an 0 ≤ Submission.Aseq N := by
      rw [Submission.Aseq]
      exact Finset.single_le_sum (f := Submission.an) (fun i _ => Nat.zero_le _) hmem
    have h1 : Submission.an 0 = 1 := Submission.ASP.FIa_zero
    have : (1 : ℕ) ≤ Submission.Aseq N := by rw [← h1]; exact hle
    exact_mod_cast this
  rw [h2]; linarith

/-- `AcountF N = Aseq N − 1`. -/
lemma AcountF_eq (N : ℕ) : AcountF N = (Submission.Aseq N : ℝ) - 1 := by
  rw [AcountF, Submission.ASP.FI_Acount_eq]

/-- The integer-pair count is `Aseq`. -/
lemma Aseq_eq_ncard (N : ℕ) :
    (Submission.Aseq N : ℝ) = (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (N : ℤ)}).ncard : ℝ) := by
  rw [Submission.Aseq]
  have h := Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_intpairs_ncard N
  rw [← h]
  push_cast
  rfl

/-- The algebraic step of the main-term identification: if `|a - b| ≤ C` then
`|(1/4)((4/π)(a-1)) - b/π| ≤ (C+1)/π`. -/
lemma main_term_step {a b C : ℝ} (h : |a - b| ≤ C) :
    |(1 / 4) * ((4 / Real.pi) * (a - 1)) - b / Real.pi| ≤ (C + 1) / Real.pi := by
  have h1 : (1 / 4 : ℝ) * ((4 / Real.pi) * (a - 1)) - b / Real.pi
      = ((a - b) - 1) / Real.pi := by ring
  rw [h1, abs_div, abs_of_pos Real.pi_pos]
  have h2 : |(a - b) - 1| ≤ C + 1 := by
    have h3 := abs_sub_le (a - b) 0 1
    have h4 : |(a - b) - 0| = |a - b| := by rw [sub_zero]
    rw [h4] at h3
    simp only [zero_sub, abs_neg, abs_one] at h3
    linarith
  exact div_le_div_of_nonneg_right h2 Real.pi_pos.le

/-- **The challenge from the chain's prime-sum bound.**  This is the final step of the assembly:
the paper's Theorem 1 for `a` (an *existential* constant `C`, as the chain produces) already
dominates the linear threshold `1.11·N^{3/4}` that
`Submission.friedlander_iwaniec_of_prime_sum_lower` consumes, because the strict numerical margin
`4κ/π − 1.11 > 0` absorbs every fixed `C` (`Submission.one_lt_four_pi_kappa`). -/
theorem challenge_of_primeSumBound (hb : PrimeSumBound) : ChallengeTheorem := by
  obtain ⟨C, hC, hbound⟩ := hb
  obtain ⟨C₂, hC₂, hCab⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_intpairs_asymptotic
  have hκ : 0 < Submission.kappa := by
    have h := Submission.four_pi_kappa_pos
    have h4 : (0 : ℝ) < 4 / Real.pi := by positivity
    nlinarith [h, h4]
  have hmargκ : (1.11 : ℝ) < 4 * Submission.kappa / Real.pi := by
    have h := Submission.one_lt_four_pi_kappa
    have h4 : (0 : ℝ) < 4 / Real.pi := by positivity
    have h5 : 4 / Real.pi * Submission.kappa = 4 * Submission.kappa / Real.pi := by ring
    linarith [h, h5.symm.le, h5.le]
  have hmarg := Work.FITop.MarginArith Submission.kappa C C₂ hκ hmargκ hC hC₂
  apply Submission.friedlander_iwaniec_of_prime_sum_lower
  filter_upwards [hbound, hmarg, Filter.eventually_ge_atTop 3] with N hbN hmargN hN3
  have hN1 : 1 ≤ N := by omega
  have hNpos : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNpos
  have hratio : 0 ≤ Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) := by
    have h3' : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
    have h1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by
      rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (N : ℝ))]
      exact le_trans (le_of_lt Real.exp_one_lt_three) h3'
    exact div_nonneg (Real.log_nonneg h1) hlogN.le
  have hquarter : Submission.primeSum N = (1 / 4) * primeSumFI N :=
    Submission.ASP.primeSum_eq_quarter N
  have hkappa : Submission.kappa = ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) := rfl
  have hCabN : |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (N : ℤ)}).ncard : ℝ)
      - 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (N : ℝ) ^ ((3 : ℝ) / 4)|
      ≤ C₂ * Real.sqrt (N : ℝ) := hCab N hN1
  have hlow : 4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4) - C₂ * Real.sqrt (N : ℝ)
      ≤ (Submission.Aseq N : ℝ) := by
    rw [Aseq_eq_ncard N, hkappa]
    linarith [(abs_le.mp hCabN).1]
  have hsupp : (Submission.Aseq N : ℝ) ≤ 4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4)
      + C₂ * Real.sqrt (N : ℝ) := by
    rw [Aseq_eq_ncard N, hkappa]
    linarith [(abs_le.mp hCabN).2]
  have hupp : AcountTil N ≤ 4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4)
      + C₂ * Real.sqrt (N : ℝ) :=
    le_trans (AcountTil_le_Aseq N) hsupp
  have hmainlow : (4 / Real.pi) * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4)
        - C₂ * Real.sqrt (N : ℝ)) - 4 / Real.pi ≤ (4 / Real.pi) * AcountF N := by
    have h1 : (4 / Real.pi) * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4)
          - C₂ * Real.sqrt (N : ℝ)) ≤ (4 / Real.pi) * (Submission.Aseq N : ℝ) :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    rw [AcountF_eq]
    linarith
  have hErr : C * AcountTil N * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      ≤ C * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4) + C₂ * Real.sqrt (N : ℝ))
          * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupp hC.le) hratio
  have hFIlow : (4 / Real.pi) * AcountF N - C * AcountTil N
        * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      ≤ primeSumFI N := by
    have := (abs_le.mp hbN).1
    linarith
  have hkey : (1 / 4) * ((4 / Real.pi) * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4)
          - C₂ * Real.sqrt (N : ℝ))
        - C * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4) + C₂ * Real.sqrt (N : ℝ))
            * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
        - 4 / Real.pi)
      ≤ (1 / 4) * primeSumFI N := by
    have h4 : (0 : ℝ) < 1 / 4 := by norm_num
    have h5 : (1 / 4) * ((4 / Real.pi) * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4)
            - C₂ * Real.sqrt (N : ℝ)) - 4 / Real.pi
          - C * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4) + C₂ * Real.sqrt (N : ℝ))
              * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)))
        ≤ (1 / 4) * ((4 / Real.pi) * AcountF N - C * AcountTil N
            * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ h4.le
      linarith [hmainlow, hErr]
    have h6 : (1 / 4) * ((4 / Real.pi) * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4)
            - C₂ * Real.sqrt (N : ℝ))
          - C * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4) + C₂ * Real.sqrt (N : ℝ))
              * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
          - 4 / Real.pi)
        = (1 / 4) * ((4 / Real.pi) * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4)
              - C₂ * Real.sqrt (N : ℝ)) - 4 / Real.pi
            - C * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4) + C₂ * Real.sqrt (N : ℝ))
                * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) := by ring
    rw [h6]
    linarith [h5, hFIlow]
  calc (1.11 : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (1 / 4) * ((4 / Real.pi) * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4)
            - C₂ * Real.sqrt (N : ℝ))
          - C * (4 * Submission.kappa * (N : ℝ) ^ ((3 : ℝ) / 4) + C₂ * Real.sqrt (N : ℝ))
              * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
          - 4 / Real.pi) := hmargN
    _ ≤ (1 / 4) * primeSumFI N := hkey
    _ = Submission.primeSum N := by rw [hquarter]

end

end Work.FIFinal
