import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.P13_tau_bound

namespace Work.FIArea4

open scoped BigOperators

/-- Bookkeeping for `P13_Ener_le`: for `r ∈ [1, 2R]` and `1 ≤ S`, the factor `r^ε` is at most
`2^ε (RS)^ε`.  This is what lets the divisor bound `τ(r) ≪_ε r^ε` be absorbed into the
`(RS)^ε`-factor of the statement. -/
lemma P13_rpow_le_two_mul (R S r : ℕ) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hr : r ∈ Finset.Icc 1 (2 * R)) {ε : ℝ} (hε : 0 < ε) :
    (r : ℝ) ^ ε ≤ (2 : ℝ) ^ ε * (((R : ℝ) * (S : ℝ)) ^ ε) := by
  have hrle : r ≤ 2 * R := (Finset.mem_Icc.mp hr).2
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hrle' : (r : ℝ) ≤ 2 * ((R : ℝ) * (S : ℝ)) := by
    have h : (r : ℝ) ≤ ((2 * R : ℕ) : ℝ) := by exact_mod_cast hrle
    push_cast at h
    nlinarith [h, hR1, hS1]
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hRS0 : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) := by positivity
  have h := Real.rpow_le_rpow hr0 hrle' (le_of_lt hε)
  rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hRS0] at h

/-- **The energy/`L²` comparison of `FIArea4`.**  The `τ(r)`-weighted energy `p14Ener` is bounded
by a constant (depending on `ε`) times `(RS)^ε` times the plain `L²`-mass `p14L2`.  This is the
elementary step that lets the `τ`-weight produced by FI Proposition 14.1's energy normalisation be
passported back to the `L²` normalisation of Propositions 11.1/13.1 at the cost of an
`(RS)^ε`-factor. -/
theorem P13_Ener_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ R → 1 ≤ S →
      p14Ener R S α ≤ C * (((R : ℝ) * (S : ℝ)) ^ ε) * p14L2 R S α := by
  obtain ⟨C, hCpos, hC⟩ := P13_tau_bound ε hε
  refine ⟨C * (2 : ℝ) ^ ε, ?_, ?_⟩
  · have : (0 : ℝ) < (2 : ℝ) ^ ε := Real.rpow_pos_of_pos (by norm_num) ε
    positivity
  · intro R S α hR hS
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ ε := Real.rpow_pos_of_pos (by norm_num) ε
    have hRSpos : (0 : ℝ) < (R : ℝ) * (S : ℝ) := by nlinarith
    have hRSnonneg : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) := le_of_lt hRSpos
    set K : ℝ := C * (2 : ℝ) ^ ε * (((R : ℝ) * (S : ℝ)) ^ ε) with hKdef
    have hpoint : ∀ r ∈ Finset.Icc 1 (2 * R), ∀ s ∈ Finset.Icc 1 (2 * S),
        ((r.divisors.card : ℕ) : ℝ) * Complex.normSq (α r s)
          ≤ K * Complex.normSq (α r s) := by
      intro r hr s _
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hτ : ((r.divisors.card : ℕ) : ℝ) ≤ C * (r : ℝ) ^ ε := hC r hr1
      have hpow := P13_rpow_le_two_mul R S r hR hS hr hε
      have hb : ((r.divisors.card : ℕ) : ℝ) ≤ K := by
        calc ((r.divisors.card : ℕ) : ℝ) ≤ C * (r : ℝ) ^ ε := hτ
          _ ≤ C * ((2 : ℝ) ^ ε * (((R : ℝ) * (S : ℝ)) ^ ε)) :=
              mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
          _ = K := by rw [hKdef]; ring
      exact mul_le_mul_of_nonneg_right hb (Complex.normSq_nonneg _)
    unfold p14Ener p14L2
    calc ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
            ((r.divisors.card : ℕ) : ℝ) * Complex.normSq (α r s)
        ≤ ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
            K * Complex.normSq (α r s) :=
          Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun s hs => hpoint r hr s hs))
      _ = K * ∑ r ∈ Finset.Icc 1 (2 * R),
            ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [Finset.mul_sum]
      _ = (C * (2 : ℝ) ^ ε) * (((R : ℝ) * (S : ℝ)) ^ ε)
            * ∑ r ∈ Finset.Icc 1 (2 * R),
                ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s) := by
          rw [hKdef]

end Work.FIArea4
