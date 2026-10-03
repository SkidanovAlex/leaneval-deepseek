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
import Submission.Work.FITop.RangeCheckChain
import Submission.ASP.S30
import Submission.Work.FITop.WolkeSquarefreeTau
import Submission.Work.FITop.AdTauAggregate
import Submission.Work.FITop.WindowRangeMarginsChain
import Submission.Work.FITop.BformAtilEqXsum
import Submission.Work.FITop.AtilTauPowFourLe
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FITop.SumIteDivDvd

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FITop

open Finset Filter
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Elementary helpers -/

lemma atilFIa_nonneg_BD (n : ℕ) : 0 ≤ atilFIa n := by
  rw [atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
  exact mul_nonneg (by positivity) (Nat.cast_nonneg _)

lemma one_le_AcountAtil_BD {x : ℕ} (hx : 1 ≤ x) : (1 : ℝ) ≤ AcountAtil x := by
  rw [AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_rfl, hx⟩
  have hsum := Finset.single_le_sum (f := atilFIa) (fun i _ => atilFIa_nonneg_BD i) hmem
  have h1 : (1 : ℝ) ≤ atilFIa 1 := by
    rw [atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
    have h : (1 : ℝ) ≤ (Submission.an 1 : ℝ) := by
      exact_mod_cast Submission.ASP.an_one_pos'
    have hmu : ((ArithmeticFunction.moebius 1 : ℝ)) ^ 2 = 1 := by
      rw [ArithmeticFunction.moebius_apply_one]; norm_num
    rw [hmu, one_mul]
    exact h
  exact le_trans h1 hsum

lemma sqrt_le_self_BD {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  refine Real.sqrt_le_iff.mpr ⟨hx0, ?_⟩
  nlinarith

lemma exp_form_BD (L : ℝ) :
    L ^ (2 ^ 17) = L ^ ((2 : ℝ) ^ (17 : ℕ)) := by
  rw [show ((2 : ℝ) ^ (17 : ℕ)) = ((2 ^ 17 : ℕ) : ℝ) by norm_num]
  exact (Real.rpow_natCast L (2 ^ 17)).symm

/-! ## The window lemma -/

end

end Work.FITop
