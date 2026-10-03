/-
  Companion paper, §9: **(R₃) for the companion's remainder at an arbitrary logarithmic exponent**.

  `FIr_cubefree_sum_le` (`S29`) bounds `∑_{d < R3cut x, cubefree}|FIr d t|` by
  `4·Aseq x·(log x)^{−2^25}`.  The Hölder step which passes from `(R)` to `(R′)` for the
  squarefree-supported sequence `ã` (see `S2b.Rprime_of_R_and_23'`) requires `(R)` at an exponent
  `λ ≥ 3θ + 12` where `θ = 2^48` is the exponent of `(2.3)`; since our `(2.1)/(2.3)` chain is
  cruder than the paper's, the relevant exponent is far larger than `2^25`.  The whole
  `Prop. 3.5` machinery (`R3_four_part_generic`, `X2Y4_R3_generic`) is therefore re-run here with
  an ARBITRARY exponent `lamm`, and the polylog bookkeeping is absorbed by the power saving of
  `(3.3)` (`D^{1/4}x^{9/16+1/100}` against `Aseq x ≍ x^{3/4}`).
-/
import Mathlib
import Submission.ASP.S30
import Submission.ASP.S22

set_option maxHeartbeats 3200000

namespace Submission.ASP

open Finset

noncomputable section

/-- **(R₃) for the companion's remainder `r_d = A_d − g d·A`**, at an arbitrary log exponent. -/
theorem FIr_cubefree_sum_le_generic (lamm : ℝ) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |FIr d t|)
        ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
  obtain ⟨X1, h1⟩ := X2Y4_R3_all_generic lamm
  obtain ⟨cA, hcA, XA, hAlow⟩ := exists_const_mul_rpow_le_Aseq
  obtain ⟨X2, hX2, htail⟩ := Submission.X2Y4R3.poly_tail_gen 1 ((7 : ℝ) / 10)
    ((2 : ℝ) ^ 25) cA lamm (by norm_num) (by norm_num) hcA
  refine ⟨max X1 (max XA X2), fun x hx t ht2 htx => ?_⟩
  have hx1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hxA : XA ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hlog0 : (0 : ℝ) ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  have hlnn : 0 ≤ (Real.log x) ^ (-lamm) := Real.rpow_nonneg hlog0 _
  -- piece 1: the main paper's remainder
  have hp1 : (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |rMain d t|)
      ≤ 2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
    have h := h1 x hx1 t ht2 htx
    have hsum : (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |rMain d t|)
        = ∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter
            (fun d => ∀ p ∈ d.primeFactors, d.factorization p ≤ 2),
            |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)| := by
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [rMain, FIg]
    rw [hsum]
    calc (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter
            (fun d => ∀ p ∈ d.primeFactors, d.factorization p ≤ 2),
            |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ 2 * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) := h
      _ = 2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by ring
  -- piece 2: the discrepancy `FIg d − 1`
  have hp2 : (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN,
        |FIg d - 1|) ≤ (Submission.X2Y4R3.R3cut x : ℝ) := by
    refine le_trans (Finset.sum_le_sum (fun d _ => FIg_sub_one_abs_le d)) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((((Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN).card : ℕ) : ℝ)
        ≤ ((Submission.X2Y4R3.R3cut x : ℕ) : ℝ) := by
      have := Finset.card_filter_le (Finset.range (Submission.X2Y4R3.R3cut x)) CubefreeN
      rw [Finset.card_range] at this
      exact_mod_cast this
    exact hcard
  have hp2' : (Submission.X2Y4R3.R3cut x : ℝ) ≤ (Submission.Aseq x : ℝ) *
      (Real.log x) ^ (-lamm) := by
    have hthis := htail x hx2
    simp only [one_mul] at hthis
    have hR3 : ((Submission.X2Y4R3.R3cut x : ℕ) : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) *
        (Real.log x) ^ ((2 : ℝ) ^ 25) := by
      rw [Submission.X2Y4R3.R3cut]
      exact_mod_cast Nat.floor_le (by positivity)
    refine le_trans hR3 ?_
    refine le_trans hthis ?_
    have hA := hAlow x hxA
    exact mul_le_mul_of_nonneg_right hA hlnn
  calc (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |FIr d t|)
      ≤ ∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN,
          (|rMain d t| + |FIg d - 1|) :=
        Finset.sum_le_sum (fun d _ => FIr_abs_le d t)
    _ = (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |rMain d t|)
        + (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |FIg d - 1|) :=
        Finset.sum_add_distrib
    _ ≤ 2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)
        + (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
        add_le_add hp1 (le_trans hp2 hp2')
    _ ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
        have hA : 0 ≤ (Submission.Aseq x : ℝ) := by positivity
        have hl : 0 ≤ (Real.log x) ^ (-lamm) := hlnn
        nlinarith [hA, hl]

end

end Submission.ASP
