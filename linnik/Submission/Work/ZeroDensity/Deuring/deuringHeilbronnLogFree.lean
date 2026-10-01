import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.repelOwnCount
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.ZeroDensity.Deuring.multCount_le_famCount
import Submission.Work.ZeroDensity.Deuring.restCount_eq_zero_of_lt_repulsion

namespace Work.ZeroDensity.Deuring

open DirichletCharacter Complex
open scoped Classical BigOperators

open Work.ZeroDensity
open Work.LinnikContract

/-- **`restCount` is a sub-count of `multCount`.**  Dropping the exclusion of the exceptional pair
`(χ₁,β₁)` and the (equivalent) reordering of the conditions can only increase the count: the
summand of `restCount` vanishes whenever the summand of `multCount` does, and where both are
non-zero they agree.  This is the step (1) of the Deuring--Heilbronn reduction, in its elementary
form; it needs no hypothesis at all. -/
theorem restCount_le_multCount {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    (t : ℝ) : restCount χ₁ β₁ t ≤ multCount q t := by
  rw [restCount, Work.LinnikAreas.Siegel.pairCount, multCount]
  refine Finset.sum_le_sum (fun χ _ => ?_)
  refine finsum_le_finsum' ?_ ?_ (fun ρ => ?_)
  · -- finite support of the `restCount` summand
    refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ 0 1).subset ?_
    intro ρ hρ
    have hc : zeroMult χ ρ ≠ 0 ∧ lamOf q ρ ≤ t ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = β₁) := by
      by_contra hcon
      exact hρ (if_neg hcon)
    obtain ⟨hz, -, hi, -⟩ := hc
    exact ⟨hz, le_of_lt (Work.LinnikAreas.zeroMult_re_pos χ hz),
      le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hz), hi⟩
  · -- finite support of the `multCount` summand
    refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ 0 1).subset ?_
    intro ρ hρ
    have hc : zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ lamOf q ρ ≤ t := by
      by_contra hcon
      exact hρ (if_neg hcon)
    obtain ⟨hz, hi, -⟩ := hc
    exact ⟨hz, le_of_lt (Work.LinnikAreas.zeroMult_re_pos χ hz),
      le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hz), hi⟩
  · -- pointwise comparison
    by_cases h : zeroMult χ ρ ≠ 0 ∧ lamOf q ρ ≤ t ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = β₁)
    · rw [if_pos h, if_pos ⟨h.1, h.2.2.1, h.2.1⟩]
    · rw [if_neg h]
      split
      · exact Nat.cast_nonneg _
      · exact le_refl 0

/-- The Deuring-Heilbronn log-free zero count with the lambda_1 factor, in the working region |Im rho| <= 1, reduced to a log-free family zero count and the repulsion with an explicit constant. Assume (i) `hcount : Work.ZeroDensity.LogFreeFamHalf (5/2)`, i.e. there are C > 0 and q_0 with `famCount q sigma 1 <= C*exp((5/2)*((1-sigma)*log q))` for all q >= q_0 and 0 <= sigma <= 1, and (ii) `hrep : Work.ZeroDensity.RepulsionWith (7/16)`, i.e. for all large q, every real character chi_1 mod q with exceptional real zero beta_1 (chi_1 != 1, chi_1^2 = 1, beta_1 < 1, zeroMult chi_1 beta_1 != 0, lambda(beta_1) <= 1/2) satisfies (7/16)*log(1/lambda(beta_1)) <= lambda(rho) for every further zero rho of any character mod q with |Im rho| <= 1. Conclude `Work.ZeroDensity.DHLogFreeSpec`: there is c < 49/10 with `restCount chi_1 beta_1 t <= C'*lambda(beta_1)*e^(c*t)` for all t with 0 < t <= log q. Route: (1) `restCount` (the pair count with lambda <= t and |Im rho| <= 1, excluding the pair (chi_1,beta_1)) is at most `Work.ZeroDensity.multCount q t` (the same count without the exclusion and with the principal character included), which is at most `famCount q (1 - t/log q) 1` because `lambda(rho) <= t` means `Re rho >= 1 - t/log q` and zeros have Re rho < 1 (the latter is `Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one`); (2) by (i) that is at most `C*e^((5/2)*t)` for 0 <= t <= log q, and for t > log q it is at most `famCount q 0 1 <= C*e^((5/2)*log q) <= C*e^((5/2)*t)`; (3) by (ii) every counted zero has `lambda(rho) >= (7/16)*log(1/lambda(beta_1))`, so the count vanishes below that threshold, and the elementary two-exponential matching `Work.LinnikAreas.ownCount_le_of_threshold_and_logfree` (already proved in the workspace) gives `restCount chi_1 beta_1 t <= C*lambda(beta_1)*e^((5/2 + 16/7)*t)`; now `5/2 + 16/7 = 67/14 = 4.785... < 49/10 = 4.9`. -/
theorem deuringHeilbronnLogFree (hcount : Work.ZeroDensity.LogFreeFamHalf (5/2))
    (hrep : Work.ZeroDensity.RepulsionWith (7/16)) : Work.ZeroDensity.DHLogFreeSpec := by
  -- the two constants and the two thresholds of the inputs
  obtain ⟨C, hCpos, qc, hcount'⟩ := hcount
  obtain ⟨qr, hrep'⟩ := hrep
  -- the exponent `c = 5/2 + 16/7 = 67/14 < 49/10`
  refine ⟨5/2 + 16/7, by norm_num, C, hCpos, max (max qc qr) 2, ?_⟩
  intro q hq _inst χ₁ β₁ hχ₁ hsq hβ₁ hzm hlam t ht _htlog
  have hqc : qc ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqr : qr ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  -- `λ(β₁) = (1-β₁)·log q > 0`
  have hlam1pos : 0 < lamOf q (β₁ : ℂ) := by
    rw [lamOf, Complex.ofReal_re]
    exact mul_pos (by linarith) hlogq
  -- the two-exponential matching of `ownCount_le_of_threshold_and_logfree`
  have hmain := Work.LinnikAreas.ownCount_le_of_threshold_and_logfree
      (N := fun t => restCount χ₁ (β₁ : ℂ) t)
      (lam₁ := lamOf q (β₁ : ℂ)) (D := C) (c₃ := 5/2) (c_r := 7/16)
      hCpos hlam1pos (by norm_num) ?_ ?_ t (le_of_lt ht)
  · rwa [show (5:ℝ)/2 + 1/(7/16) = 5/2 + 16/7 by norm_num] at hmain
  · -- (3) below the Deuring--Heilbronn threshold the count vanishes
    intro t' ht'
    exact restCount_eq_zero_of_lt_repulsion
      (fun χ ρ hz him hne => hrep' q hqr χ₁ β₁ hχ₁ hsq hβ₁ hzm hlam χ ρ hz him hne) ht'
  · -- (1)+(2) the log-free bound `N t' ≤ C e^{(5/2)t'}` for `t' ≥ 0`
    intro t' ht'
    have hσ0 : 0 ≤ max 0 (1 - t' / Real.log q) := le_max_left _ _
    have hσ1 : max 0 (1 - t' / Real.log q) ≤ 1 := by
      refine max_le (by norm_num) ?_
      have : 0 ≤ t' / Real.log q := div_nonneg ht' (le_of_lt hlogq)
      linarith
    -- `restCount ≤ multCount ≤ famCount q σ 1`, `σ = max 0 (1 - t'/log q)`
    have hstep : restCount χ₁ (β₁ : ℂ) t' ≤ famCount q (max 0 (1 - t' / Real.log q)) 1 :=
      le_trans (restCount_le_multCount χ₁ (β₁ : ℂ) t') (multCount_le_famCount hq2 t')
    -- the log-free family count at `σ`
    have hfam := hcount' q hqc (max 0 (1 - t' / Real.log q)) hσ0 hσ1
    -- `(1-σ)·log q = min (log q) t' ≤ t'`
    have hem : 1 - max 0 (1 - t' / Real.log q) ≤ t' / Real.log q := by
      rcases le_total 0 (1 - t' / Real.log q) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hexp_le : (1 - max 0 (1 - t' / Real.log q)) * Real.log q ≤ t' := by
      have h1 : (1 - max 0 (1 - t' / Real.log q)) * Real.log q
          ≤ (t' / Real.log q) * Real.log q :=
        mul_le_mul_of_nonneg_right hem (le_of_lt hlogq)
      have h2 : (t' / Real.log q) * Real.log q = t' := by field_simp
      linarith
    calc restCount χ₁ (β₁ : ℂ) t' ≤ famCount q (max 0 (1 - t' / Real.log q)) 1 := hstep
      _ ≤ C * Real.exp ((5/2) * ((1 - max 0 (1 - t' / Real.log q)) * Real.log q)) := hfam
      _ ≤ C * Real.exp ((5/2) * t') := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_of_lt hCpos)
          exact mul_le_mul_of_nonneg_left hexp_le (by norm_num)

end Work.ZeroDensity.Deuring
