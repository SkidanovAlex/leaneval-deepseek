import Submission.PVer1Base
import Submission.ScaleBoundAny
import Submission.PVer1LowerPos
import Submission.PVer1LowerLeft
import Submission.PVer1LowerRight
import Submission.PVer1UpperPtw

/-!
# Assembly of `lem:P_ver1` (2) and (3)

This module re-declares the two main theorems of the `PVer1` development
(definitions and analytic lemmas live in `Submission.PVer1Base`, the four
case lemmas in `Submission.PVer1LowerPos`, `…LowerLeft`, `…LowerRight`,
`…UpperPtw`) and proves them by combining the cases:

* `weighted_lower_bound`: split at the roots of `P_{N+2}` (kept roots give
  `0 ≤ 0`, the two extreme roots are handled by `lower_left_root` /
  `lower_right_root`, all other points by `lower_pos`), take the maximum of
  the three `∃`-constants.
* `weighted_norm_bound`: the pointwise bound `upper_ptwise` plus
  `wnorm_sSup_le` gives `wnorm (N+s) P̃ ≤ e^{Kshift}·(N+2)^{Cu}·Cc`, and
  `scale_bound_up_any` turns the right hand side into `N^C`.
-/

noncomputable section

open MeasureTheory
open Filter
open scoped Real BigOperators Topology
open Polynomial

namespace Submission.PVer1

open Submission.PotentialDefs
open Submission.SerreExample
open Submission.PotentialContinuity
open Submission.Quantile
open Submission.QuantileExt
open Submission.ThreePages
open Submission.Bclps
open Submission.Contracts
open Submission.WeightedNorm
open Submission.WnormShift
open Submission.WnormToolkit
open Submission.ScaleBoundLower
open Submission.ScaleBoundUpper
open Submission.ScaleBoundAny
open Submission.PVer1LowerPos
open Submission.PVer1LowerLeft
open Submission.PVer1LowerRight
open Submission.PVer1UpperPtw

/-- **lem:P_ver1(2)** — weighted lower bound:
`∃ C, 0 < C ∧ ∀ N ≥ 2, ∀ s ≤ Bclps.Dconst, ∀ x ∈ Icc aSerre bSerre :
   (N:ℝ)^{-C}·rhoKept N x ≤ w_μ(x)^{N+s}·|P̃_N(x)|` (at roots both sides are 0). -/
theorem weighted_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ s : ℕ, s ≤ Bclps.Dconst →
      ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
        (N : ℝ) ^ (-C) * rhoKept N x ≤
          (weight muS x) ^ (N + s) * |(prunePoly N).eval x| := by
  rcases lower_pos with ⟨C0, hC0pos, hC0⟩
  rcases lower_left_root with ⟨C1, hC1pos, hC1⟩
  rcases lower_right_root with ⟨C2, hC2pos, hC2⟩
  let C : ℝ := max (max C0 C1) C2
  have hle0 : C0 ≤ C := by dsimp [C]; exact le_trans (le_max_left C0 C1) (le_max_left (max C0 C1) C2)
  have hle1 : C1 ≤ C := by dsimp [C]; exact le_trans (le_max_right C0 C1) (le_max_left (max C0 C1) C2)
  have hle2 : C2 ≤ C := by dsimp [C]; exact le_max_right (max C0 C1) C2
  have hCpos : 0 < C := lt_of_lt_of_le hC0pos hle0
  refine ⟨C, hCpos, ?_⟩
  intro N hN s hs x hx
  have hmono : ∀ {c : ℝ}, c ≤ C → (N : ℝ) ^ (-C) ≤ (N : ℝ) ^ (-c) := by
    intro c hc
    have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
    rw [Real.rpow_def_of_pos hNpos, Real.rpow_def_of_pos hNpos]
    exact Real.exp_le_exp.mpr (by
      have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
      have hne : -C ≤ -c := by linarith
      exact mul_le_mul_of_nonneg_left hne hlog)
  have hρKept0 : 0 ≤ rhoKept N x := rhoKept_nonneg N x
  by_cases hρpos : 0 < rhoFull N x
  · have hmain := hC0 N hN s hs x hx hρpos
    have hm := mul_le_mul_of_nonneg_right (hmono hle0) hρKept0
    -- hm : N^{-C}·ρKept ≤ N^{-C0}·ρKept
    exact le_trans hm hmain
  · have hρ0 : rhoFull N x = 0 := by
      apply le_antisymm
      · exact le_of_not_gt hρpos
      · unfold rhoFull
        exact rho_nonneg (n := N + 2) x
    have hn : 1 ≤ N + 2 := by omega
    rcases exists_index_rho (n := N + 2) hn x with ⟨i, hi, hatt⟩
    have hxeq : x = alpha (N + 2) i := by
      have hatt' : rhoFull N x = |x - alpha (N + 2) i| := by
        unfold rhoFull
        exact hatt
      rw [hρ0] at hatt'
      have hz : |x - alpha (N + 2) i| = 0 := hatt'.symm
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    rw [Finset.mem_Icc] at hi
    by_cases hEq1 : i = 1
    · subst i
      have hmain := hC1 N hN s hs
      rw [hxeq]
      have hm := mul_le_mul_of_nonneg_right (hmono hle1) (rhoKept_nonneg N (alpha (N + 2) 1))
      exact le_trans hm hmain
    · by_cases hEqT : i = N + 2
      · subst i
        have hmain := hC2 N hN s hs
        rw [hxeq]
        have hm := mul_le_mul_of_nonneg_right (hmono hle2) (rhoKept_nonneg N (alpha (N + 2) (N + 2)))
        exact le_trans hm hmain
      · have ik : i ∈ kept N := by
          unfold kept
          rw [Finset.mem_Icc]
          omega
        rw [hxeq]
        have hρK : rhoKept N (alpha (N + 2) i) = 0 := by
          apply le_antisymm
          · unfold rhoKept
            rw [dif_pos (kept_nonempty (by omega : 1 ≤ N))]
            calc
              (kept N).inf' (kept_nonempty (by omega : 1 ≤ N))
                  (fun j => |alpha (N + 2) i - alpha (N + 2) j|)
                  ≤ |alpha (N + 2) i - alpha (N + 2) i| :=
                    Finset.inf'_le (fun j => |alpha (N + 2) i - alpha (N + 2) j|) ik
              _ = 0 := by simp
          · exact rhoKept_nonneg N (alpha (N + 2) i)
        have hP : (prunePoly N).eval (alpha (N + 2) i) = 0 := by
          rw [prunePoly_eval N (alpha (N + 2) i)]
          exact Finset.prod_eq_zero ik (by ring)
        rw [hρK]
        simp [hP]

/-- **lem:P_ver1(3)** — weighted norm upper bound:
`∃ C, 0 < C ∧ ∀ N ≥ 2, ∀ s ≤ Bclps.Dconst :
   wnorm (N+s) (prunePoly N) ≤ (N:ℝ)^C`. -/
theorem weighted_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ s : ℕ, s ≤ Bclps.Dconst →
      wnorm (N + s) (prunePoly N) ≤ (N : ℝ) ^ C := by
  rcases upper_ptwise with ⟨Cu, Cc, hCupos, hCcpos, hup⟩
  rcases (scale_bound_up_any Cu Kshift Cc hCupos Kshift_nonneg hCcpos) with ⟨C, hCpos, hscale⟩
  refine ⟨C, hCpos, ?_⟩
  intro N hN s hs
  have hpt : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      (weight muSerre x) ^ (N + s) * |(prunePoly N).eval x| ≤
        Real.exp Kshift * ((N + 2 : ℕ) : ℝ) ^ Cu * Cc := hup N hN s hs
  have hwn : wnorm (N + s) (prunePoly N) ≤
      Real.exp Kshift * ((N + 2 : ℕ) : ℝ) ^ Cu * Cc := by
    apply wnorm_sSup_le (k := N + s) (P := prunePoly N)
    intro x hx
    exact hpt x hx
  have hsc := hscale N hN
  exact le_trans hwn hsc

end Submission.PVer1
