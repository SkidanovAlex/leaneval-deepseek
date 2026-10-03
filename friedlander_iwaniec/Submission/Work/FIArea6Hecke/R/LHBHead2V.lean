import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators

noncomputable section

/-- `n^{-2} = 1/n²` for a natural number, in real powers. -/
private lemma rpow_neg_two_eq (n : ℕ) :
    (n : ℝ) ^ (-2 : ℝ) = 1 / (n : ℝ) ^ 2 := by
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  simp [one_div]

/-- The Dirichlet series `Σ_n τ(n)/n²` converges, and its terms are nonnegative. -/
private lemma summable_tau_div_sq :
    Summable (fun n : ℕ => ((Nat.divisors n).card : ℝ) * (n : ℝ) ^ (-2 : ℝ)) :=
  Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg (by norm_num : (1 : ℝ) < 2)

private lemma tau_term_nonneg (n : ℕ) :
    (0 : ℝ) ≤ ((Nat.divisors n).card : ℝ) * (n : ℝ) ^ (-2 : ℝ) :=
  mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The total mass `Στ(n)/n²` is at least `1`. -/
private lemma one_le_tsum_tau :
    (1 : ℝ) ≤ ∑' n : ℕ, ((Nat.divisors n).card : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by
  have h := Summable.sum_le_tsum ({1} : Finset ℕ) (fun i _ => tau_term_nonneg i) summable_tau_div_sq
  simpa using h

-- NOTE for the prover: do NOT import `Submission.Work.FIArea6Hecke.R.LHBHead2` (its proof is a
-- `sorry`).  Prove this from scratch; the ingredients are `heckeLam` (`FIArea5/S16Hecke/Defs.lean`),
-- `heckeLam_bound` (`FIArea5/S16Hecke/heckeLam_bound.lean`): `‖heckeLam chi k n‖ ≤ 4 * n.divisors.card`,
-- and summability of `∑ τ(n)/n²`.
theorem LHBHead2V :
    ∃ K : ℝ, 0 < K ∧ ∀ (chi : GaussianInt → ℂ), (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      ∀ M : ℕ,
        ∑ n ∈ Finset.Icc 1 M, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ) ^ 2
          ≤ K := by
  classical
  refine ⟨4 * ∑' n : ℕ, ((Nat.divisors n).card : ℝ) * (n : ℝ) ^ (-2 : ℝ), ?_, ?_⟩
  · nlinarith [one_le_tsum_tau]
  · intro chi hchi M
    have hpt : ∀ n ∈ Finset.Icc 1 M,
        ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ) ^ 2
          ≤ 4 * (((Nat.divisors n).card : ℝ) * (n : ℝ) ^ (-2 : ℝ)) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hb := Work.FIArea5.S16Hecke.heckeLam_bound chi 0 hchi hn1
      have hpow : (n : ℝ) ^ (-2 : ℝ) = 1 / (n : ℝ) ^ 2 := rpow_neg_two_eq n
      calc ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ) ^ 2
          ≤ (4 * ((Nat.divisors n).card : ℝ)) / (n : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hb (by positivity)
        _ = 4 * (((Nat.divisors n).card : ℝ) * (n : ℝ) ^ (-2 : ℝ)) := by
            rw [hpow]; ring
    calc ∑ n ∈ Finset.Icc 1 M, ‖Work.FIArea5.S16Hecke.heckeLam chi 0 n‖ / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 M, 4 * (((Nat.divisors n).card : ℝ) * (n : ℝ) ^ (-2 : ℝ)) :=
          Finset.sum_le_sum hpt
      _ = 4 * ∑ n ∈ Finset.Icc 1 M, ((Nat.divisors n).card : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ 4 * ∑' n : ℕ, ((Nat.divisors n).card : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Summable.sum_le_tsum _ (fun i _ => tau_term_nonneg i) summable_tau_div_sq

end

end Work.FIArea6Hecke.R
