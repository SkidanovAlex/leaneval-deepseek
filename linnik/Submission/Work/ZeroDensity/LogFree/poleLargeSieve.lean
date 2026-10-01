import Mathlib
import Submission.Work.ZeroDensity.LogFree.poleLSDefs
import Submission.Work.ZeroDensity.LogFree.HB7MvtAny
import Submission.Work.ZeroDensity.LogFree.HB7CpowSplit
import Submission.Work.ZeroDensity.LogFree.HB7FreezeError
import Submission.Work.ZeroDensity.LogFree.HB7FreezeMain
import Submission.Work.ZeroDensity.LogFree.HB7FreezeIntegrable
import Submission.Work.ZeroDensity.LogFree.HB7DampedSmallIntegrable
import Submission.Work.ZeroDensity.LogFree.HB7NegSumBound
import Submission.Work.ZeroDensity.LogFree.HB7PosSumGeom
import Submission.Work.ZeroDensity.LogFree.HB7PosSumSumnable
import Submission.Work.ZeroDensity.LogFree.HB7WeightSeries
import Submission.Work.ZeroDensity.LogFree.HB7TilingIoi
import Submission.Work.ZeroDensity.LogFree.HB7DampedClassBound
import Submission.Work.ZeroDensity.LogFree.HB7ParamsRegime
import Submission.Work.ZeroDensity.HB7MvtMul
import Submission.Work.ZeroDensity.HB7PoleKIntegral
import Submission.Work.ZeroDensity.HB7PoleGramIntegrable
import Submission.Work.ZeroDensity.HB7PoleGramDoubleSum
import Submission.Work.ZeroDensity.HB7PoleGramReId

/-!
# `Work.ZeroDensity.LogFree.poleLargeSieve` — L4 of the unified log-free argument

The damped large sieve for the pole Gram matrix (Heath-Brown (1992), §11, Lemma L4), in the
`O(1)`-constant form used by `JUTILA_UNIFIED_LEAD.md` §3.
-/

open MeasureTheory Set
open scoped BigOperators Classical
noncomputable section

namespace Work.ZeroDensity.LogFree

set_option maxHeartbeats 1000000


/-! ## The weight-series arithmetic (vendored from the `HB7*` development) -/

/-- The exponential series `∑' n, min 1 (exp ((C₀ - n) L))` is summable with total mass at most
`C₀ + 4`, for `C₀ ≥ 1` and `L ≥ 1`.  This is the two-sided-truncated weight sum of the damped
small class bound. -/
theorem pls_posSumBound (C₀ L : ℝ) (hC₀ : 1 ≤ C₀) (hL : 1 ≤ L) :
    Summable (fun n : ℕ => min 1 (Real.exp ((C₀ - (n:ℝ)) * L))) ∧
    (∑' n : ℕ, min 1 (Real.exp ((C₀ - (n:ℝ)) * L))) ≤ C₀ + 4 := by
  have hLpos : 0 < L := by linarith
  set M : ℕ := ⌈C₀⌉₊ with hM
  have hC₀M : C₀ ≤ (M : ℝ) := Nat.le_ceil C₀
  have hS₁ : Summable (fun n : ℕ => min 1 (Real.exp ((C₀ - (n:ℝ)) * L))) :=
    HB7PosSumSumnable C₀ L hLpos
  have hS₂ : Summable (fun n : ℕ => min 1 (Real.exp (((M:ℝ) - (n:ℝ)) * L))) :=
    HB7PosSumSumnable (M:ℝ) L hLpos
  have hpt : ∀ n : ℕ, min 1 (Real.exp ((C₀ - (n:ℝ)) * L))
      ≤ min 1 (Real.exp (((M:ℝ) - (n:ℝ)) * L)) := by
    intro n
    refine min_le_min_left 1 ?_
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith : (0:ℝ) ≤ L)
  refine ⟨hS₁, ?_⟩
  have h1 := hS₁.tsum_le_tsum hpt hS₂
  have h2 := HB7PosSumGeom M L hL
  have hMle : (M : ℝ) ≤ C₀ + 1 := by
    have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ C₀ by linarith)
    linarith
  linarith


/-- The weight sum of Heath-Brown (1992), §7: the doubly-damped weights
`min 1 (min (K exp(-jL)) (exp(-exp(-(j+1)L))))`, damped further by
`exp(-2 a j L)` with `0 ≤ a ≤ 1/L`, are summable over `ℤ` with a total mass
bounded by a universal constant times `C₀`, uniformly in `K, L, a` subject to
`log K ≤ C₀ L`. -/
theorem pls_weightSum :
    ∃ K' : ℝ, 0 < K' ∧ ∀ (K C₀ L a : ℝ), 2 ≤ K → 1 ≤ C₀ → 1 ≤ L →
      Real.log K ≤ C₀ * L → 0 ≤ a → a ≤ 1 / L →
      Summable (fun j : ℤ => min 1 (min (K * Real.exp (-((j : ℝ) * L)))
          (Real.exp (-(Real.exp (-(((j : ℝ) + 1) * L))))))
          * Real.exp (-(2 * a * ((j : ℝ) * L)))) ∧
      (∑' j : ℤ, min 1 (min (K * Real.exp (-((j : ℝ) * L)))
          (Real.exp (-(Real.exp (-(((j : ℝ) + 1) * L))))))
          * Real.exp (-(2 * a * ((j : ℝ) * L)))) ≤ K' * C₀ := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro K C₀ L a hK hC₀ hL hlog ha0 haL
  let T : ℤ → ℝ := fun j => min 1 (min (K * Real.exp (-((j : ℝ) * L)))
      (Real.exp (-(Real.exp (-(((j : ℝ) + 1) * L)))))) * Real.exp (-(2 * a * ((j : ℝ) * L)))
  change Summable T ∧ (∑' j : ℤ, T j) ≤ 1000000 * C₀
  have hTnn : ∀ j : ℤ, 0 ≤ T j := by
    intro j
    dsimp only [T]
    have hm : 0 < min 1 (min (K * Real.exp (-((j : ℝ) * L)))
        (Real.exp (-(Real.exp (-(((j : ℝ) + 1) * L)))))) :=
      lt_min (by norm_num) (lt_min (by positivity) (Real.exp_pos _))
    exact mul_nonneg (le_of_lt hm) (Real.exp_nonneg _)
  have hpos : ∀ n : ℕ, T (n : ℤ) ≤ min 1 (Real.exp ((C₀ - (n : ℝ)) * L)) := by
    intro n
    dsimp only [T]
    have hKpos : 0 < K := by linarith
    have hKle : K ≤ Real.exp (C₀ * L) := by
      rw [← Real.exp_log hKpos]; exact Real.exp_le_exp.mpr hlog
    have hKe : K * Real.exp (-(((n:ℤ):ℝ) * L)) ≤ Real.exp ((C₀ - (n:ℝ)) * L) := by
      have hcast : (((n:ℤ):ℝ)) = (n:ℝ) := by simp
      rw [hcast]
      calc K * Real.exp (-((n:ℝ) * L)) ≤ Real.exp (C₀ * L) * Real.exp (-((n:ℝ) * L)) :=
            mul_le_mul_of_nonneg_right hKle (Real.exp_nonneg _)
        _ = Real.exp ((C₀ - (n:ℝ)) * L) := by rw [← Real.exp_add]; congr 1; ring
    have hmin1 : min 1 (min (K * Real.exp (-(((n:ℤ):ℝ) * L)))
            (Real.exp (-(Real.exp (-(((((n:ℤ):ℝ) + 1) * L))))))) ≤ 1 := min_le_left _ _
    have hmin2 : min 1 (min (K * Real.exp (-(((n:ℤ):ℝ) * L)))
            (Real.exp (-(Real.exp (-(((((n:ℤ):ℝ) + 1) * L))))))) ≤ Real.exp ((C₀ - (n:ℝ)) * L) :=
      le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) hKe
    have hA : min 1 (min (K * Real.exp (-(((n:ℤ):ℝ) * L)))
            (Real.exp (-(Real.exp (-(((((n:ℤ):ℝ) + 1) * L))))))) ≤ min 1 (Real.exp ((C₀ - (n:ℝ)) * L)) :=
      le_min hmin1 hmin2
    have hB1 : Real.exp (-(2 * a * (((n:ℤ):ℝ) * L))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0:ℝ) ≤ 2 * a * (((n:ℤ):ℝ) * L) := by positivity
      linarith
    have hBnn : 0 ≤ Real.exp (-(2 * a * (((n:ℤ):ℝ) * L))) := Real.exp_nonneg _
    have hCnn : 0 ≤ min 1 (Real.exp ((C₀ - (n:ℝ)) * L)) :=
      le_min (by norm_num) (Real.exp_nonneg _)
    calc (min 1 (min (K * Real.exp (-(((n:ℤ):ℝ) * L)))
            (Real.exp (-(Real.exp (-(((((n:ℤ):ℝ) + 1) * L)))))))
            * Real.exp (-(2 * a * (((n:ℤ):ℝ) * L))))
        ≤ min 1 (Real.exp ((C₀ - (n:ℝ)) * L)) * 1 := mul_le_mul hA hB1 hBnn hCnn
      _ = min 1 (Real.exp ((C₀ - (n:ℝ)) * L)) := mul_one _
  have hneg : ∀ n : ℕ, T (-((n:ℤ) + 1)) ≤
      Real.exp (-(Real.exp (n:ℝ))) * Real.exp (2 * ((n:ℝ) + 1)) := by
    intro n
    dsimp only [T]
    have hLpos : 0 < L := by linarith
    have haL' : a * L ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right haL (le_of_lt hLpos)
      rwa [one_div, inv_mul_cancel₀ (ne_of_gt hLpos)] at h
    rw [show ((-((n:ℤ) + 1) : ℤ) : ℝ) = -((n:ℝ)) - 1 by push_cast; ring]
    have e1 : Real.exp (-((-((n:ℝ)) - 1) * L)) = Real.exp (((n:ℝ) + 1) * L) := by congr 1; ring
    have e2 : Real.exp (-((-((n:ℝ)) - 1 + 1) * L)) = Real.exp ((n:ℝ) * L) := by congr 1; ring
    have e3 : Real.exp (-(2 * a * ((-((n:ℝ)) - 1) * L))) = Real.exp (2 * a * (((n:ℝ) + 1) * L)) := by
      congr 1; ring
    rw [e1, e2, e3]
    have hY1 : Real.exp (-(Real.exp ((n:ℝ) * L))) ≤ 1 := by
      rw [Real.exp_le_one_iff]; exact neg_nonpos.mpr (Real.exp_nonneg _)
    have hX : Real.exp (-(Real.exp ((n:ℝ) * L))) ≤ K * Real.exp (((n:ℝ) + 1) * L) := by
      have h1 : (1:ℝ) ≤ K * Real.exp (((n:ℝ) + 1) * L) := by
        have h2 : (1:ℝ) ≤ Real.exp (((n:ℝ) + 1) * L) := by
          rw [Real.one_le_exp_iff]; positivity
        nlinarith [hK, h2]
      exact le_trans hY1 h1
    rw [min_eq_right hX, min_eq_right hY1]
    have hZ : Real.exp (2 * a * (((n:ℝ) + 1) * L)) ≤ Real.exp (2 * ((n:ℝ) + 1)) := by
      rw [Real.exp_le_exp]
      have hfac : 2 * a * (((n:ℝ) + 1) * L) = 2 * ((n:ℝ) + 1) * (a * L) := by ring
      rw [hfac]
      calc 2 * ((n:ℝ) + 1) * (a * L) ≤ 2 * ((n:ℝ) + 1) * 1 := by
            apply mul_le_mul_of_nonneg_left haL'
            positivity
        _ = 2 * ((n:ℝ) + 1) := by ring
    have hY : Real.exp (-(Real.exp ((n:ℝ) * L))) ≤ Real.exp (-(Real.exp ((n:ℝ)))) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg_iff.mpr
      apply Real.exp_le_exp.mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n, hL,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (by linarith : (0:ℝ) ≤ L - 1)]
    exact mul_le_mul hY hZ (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hPosSumm : Summable (fun n : ℕ => min 1 (Real.exp ((C₀ - (n:ℝ)) * L))) :=
    (pls_posSumBound C₀ L hC₀ hL).1
  have hTpos : Summable (fun n : ℕ => T (n : ℤ)) :=
    Summable.of_nonneg_of_le (fun n => hTnn _) hpos hPosSumm
  have hTneg : Summable (fun n : ℕ => T (-((n:ℤ) + 1))) :=
    Summable.of_nonneg_of_le (fun n => hTnn _) hneg (HB7NegSumBound).1
  have hTsum : Summable T := Summable.of_nat_of_neg_add_one hTpos hTneg
  have hpos_bound : (∑' n : ℕ, T (n : ℤ)) ≤ C₀ + 4 :=
    le_trans (Summable.tsum_le_tsum hpos hTpos hPosSumm) (pls_posSumBound C₀ L hC₀ hL).2
  have hneg_bound : (∑' n : ℕ, T (-((n:ℤ) + 1))) ≤ 20000 :=
    le_trans (Summable.tsum_le_tsum hneg hTneg (HB7NegSumBound).1) (HB7NegSumBound).2
  refine ⟨hTsum, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hTpos hTneg]
  linarith [hpos_bound, hneg_bound, hC₀]

/-- `‖x + y‖ ^ 2 ≤ 2 ‖x‖ ^ 2 + 2 ‖y‖ ^ 2` for complex `x`, `y`. -/
private lemma norm_add_sq_le_two (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 := mul_self_le_mul_self (norm_nonneg (x + y)) (norm_add_le x y)
  nlinarith [h1, sq_nonneg (‖x‖ - ‖y‖)]

/-- Dividing `‖G + H‖ ^ 2` by a positive `y` and splitting into the two pieces. -/
private lemma div_split_le {y : ℝ} (G H : ℂ) (hy : 0 < y) :
    ‖G + H‖ ^ 2 / y ≤ 2 * (‖G‖ ^ 2 / y) + 2 * (‖H‖ ^ 2 / y) := by
  have h : ‖G + H‖ ^ 2 ≤ 2 * ‖G‖ ^ 2 + 2 * ‖H‖ ^ 2 := norm_add_sq_le_two G H
  have h2 := div_le_div_of_nonneg_right h (le_of_lt hy)
  rwa [show (2 * ‖G‖ ^ 2 + 2 * ‖H‖ ^ 2) / y = 2 * (‖G‖ ^ 2 / y) + 2 * (‖H‖ ^ 2 / y)
        from by ring] at h2

theorem pls_freezeBlock {C : ℝ} (hC : 0 < C) (hMVT : Work.ZeroDensity.LogFree.MvtMul C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℝ), 1 ≤ L → ∀ {ι : Type*} [Fintype ι]
      (a γ : ι → ℝ) (z : ι → ℂ) (Y : ℝ), 0 < Y →
        (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1 / L) →
        (∀ i j, i ≠ j → 1 / L ≤ |γ i - γ j|) →
        (∫ y in (Y * Real.exp (-L))..Y,
            ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
          ≤ K * L * ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i) := by
  -- The error-term bound of the freeze decomposition.
  obtain ⟨Kb, hKbpos, hKb⟩ := Work.ZeroDensity.LogFree.HB7FreezeError hC hMVT
  refine ⟨2 * (1 + C) + 2 * Kb, by linarith, ?_⟩
  intro L hL ι ιf a γ z Y hY ha0 haL hsep
  -- Integrability of the three integrands.
  obtain ⟨I1, I2, I3⟩ := HB7FreezeIntegrable (ι := ι) a γ z Y L hY
  have hYL : Y * Real.exp (-L) ≤ Y := by
    have he : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-L)]
  -- Pointwise: freeze the amplitude `y ^ a i` at `Y ^ a i`, splitting off the error term.
  have hpoint : ∀ y ∈ Set.Icc (Y * Real.exp (-L)) Y,
      ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y
        ≤ 2 * (‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ)
              * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
          + 2 * (‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (((y / Y) ^ (a i) - 1 : ℝ) : ℂ)
              * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y) := by
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le (mul_pos hY (Real.exp_pos _)) hy.1
    have hsplit : (∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I))
        = (∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))
          + (∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (((y / Y) ^ (a i) - 1 : ℝ) : ℂ)
              * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [HB7CpowSplit hY hypos]
      ring
    rw [hsplit]
    exact div_split_le _ _ hypos
  -- Monotonicity of the interval integral.
  have hstep1 : (∫ y in (Y * Real.exp (-L))..Y,
        ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      ≤ ∫ y in (Y * Real.exp (-L))..Y,
          2 * (‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ)
                * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
          + 2 * (‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (((y / Y) ^ (a i) - 1 : ℝ) : ℂ)
                * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y) :=
    intervalIntegral.integral_mono_on hYL I1 ((I2.const_mul 2).add (I3.const_mul 2)) hpoint
  -- Additivity of the interval integral.
  have hadd : (∫ y in (Y * Real.exp (-L))..Y,
          2 * (‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ)
                * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
          + 2 * (‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (((y / Y) ^ (a i) - 1 : ℝ) : ℂ)
                * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y))
      = 2 * (∫ y in (Y * Real.exp (-L))..Y,
          ‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ)
            * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
        + 2 * (∫ y in (Y * Real.exp (-L))..Y,
          ‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (((y / Y) ^ (a i) - 1 : ℝ) : ℂ)
            * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y) := by
    rw [intervalIntegral.integral_add (I2.const_mul 2) (I3.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- The two bounds.
  have hG := Work.ZeroDensity.LogFree.HB7FreezeMain hMVT L hL a γ z Y hY hsep
  have hH := hKb L hL a γ z Y hY ha0 haL hsep
  calc (∫ y in (Y * Real.exp (-L))..Y,
        ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      ≤ ∫ y in (Y * Real.exp (-L))..Y,
          2 * (‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ)
                * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
          + 2 * (‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (((y / Y) ^ (a i) - 1 : ℝ) : ℂ)
                * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y) := hstep1
    _ = 2 * (∫ y in (Y * Real.exp (-L))..Y,
          ‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ)
            * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
        + 2 * (∫ y in (Y * Real.exp (-L))..Y,
          ‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (((y / Y) ^ (a i) - 1 : ℝ) : ℂ)
            * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y) := hadd
    _ ≤ 2 * ((1 + C) * L * ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i))
        + 2 * (Kb * L * ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i)) := by linarith [hG, hH]
    _ = (2 * (1 + C) + 2 * Kb) * L * ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i) := by ring

/-! ## Auxiliary lemmas for the damped small-class bound

The proof decomposes the damped integral along the multiplicative blocks
`C_j = (X e^{-(j+1)L}, X e^{-jL}]` (`j : ℤ`), which cover `(0,∞)`; on each block the weight
`e^{-y/X} - e^{-y/U'}` is bounded by the block constant `Ψ_j`, and the *frozen* amplitude form is
controlled by `pls_freezeBlock` (which itself rests on `MvtMul C`).  The remaining arithmetic is the
one-dimensional block sum `pls_weightSum`. -/

/-- A finite sum of nonnegative summable families is summable, and `∑'` interchanges with it. -/
lemma hb7s_tsum_finset_sum_of_nonneg {ι : Type*} {g : ι → ℤ → ℝ} :
    ∀ (s : Finset ι), (∀ i ∈ s, ∀ j, 0 ≤ g i j) → (∀ i ∈ s, Summable (g i)) →
      Summable (fun j => ∑ i ∈ s, g i j) ∧ (∑' j, ∑ i ∈ s, g i j) = ∑ i ∈ s, ∑' j, g i j := by
  classical
  intro s
  induction s using Finset.induction with
  | empty =>
      intro h hS
      exact ⟨by simpa using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ))), by simp⟩
  | insert a s ha ih =>
      intro h hS
      obtain ⟨hs1, hs2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
        (fun i hi => hS i (Finset.mem_insert_of_mem hi))
      have haS : Summable (g a) := hS a (Finset.mem_insert_self a s)
      refine ⟨?_, ?_⟩
      · have heq : (fun j => ∑ i ∈ insert a s, g i j) = fun j => g a j + ∑ i ∈ s, g i j := by
          funext j; rw [Finset.sum_insert ha]
        rw [heq]; exact haS.add hs1
      · have heq : (∑' j, ∑ i ∈ insert a s, g i j) = ∑' j, (g a j + ∑ i ∈ s, g i j) := by
          congr 1; funext j; rw [Finset.sum_insert ha]
        rw [heq, haS.tsum_add hs1, hs2, Finset.sum_insert ha]

/-- The multiplicative blocks `(X e^{-(j+1)L}, X e^{-jL}]` cover `(0,∞)`. -/
lemma hb7s_iUnion_blk {X L : ℝ} (hX : 0 < X) (hL : 0 < L) :
    (⋃ j : ℤ, Set.Ioc (X * Real.exp (-(((j : ℝ) + 1) * L))) (X * Real.exp (-((j : ℝ) * L))))
      = Set.Ioi 0 := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro ⟨j, h1, h2⟩
    exact lt_trans (mul_pos hX (Real.exp_pos (-(((j : ℝ) + 1) * L)))) h1
  · intro hy
    have hyX : 0 < X / y := div_pos hX hy
    set j₀ : ℤ := ⌊Real.log (X / y) / L⌋ with hj₀
    have hfl : (j₀ : ℝ) ≤ Real.log (X / y) / L := Int.floor_le _
    have hfr : Real.log (X / y) / L < (j₀ : ℝ) + 1 := Int.lt_floor_add_one _
    have h3 : (j₀ : ℝ) * L ≤ Real.log (X / y) := by
      have h := mul_le_mul_of_nonneg_right hfl hL.le
      rwa [div_mul_cancel₀ _ hL.ne'] at h
    have h4 : Real.log (X / y) < ((j₀ : ℝ) + 1) * L := by
      have h := mul_lt_mul_of_pos_right hfr hL
      rwa [div_mul_cancel₀ _ hL.ne'] at h
    have h5 : Real.log (X / y) = Real.log X - Real.log y := Real.log_div hX.ne' hy.ne'
    refine ⟨j₀, ?_, ?_⟩
    · refine (Real.log_lt_log_iff (by positivity) hy).1 ?_
      rw [Real.log_mul hX.ne' (Real.exp_ne_zero _), Real.log_exp]
      linarith
    · refine (Real.log_le_log_iff hy (by positivity)).1 ?_
      rw [Real.log_mul hX.ne' (Real.exp_ne_zero _), Real.log_exp]
      linarith

/-- The multiplicative blocks are pairwise disjoint. -/
lemma hb7s_pairwiseDisjoint_blk {X L : ℝ} (hX : 0 < X) (hL : 0 < L) :
    Pairwise (Function.onFun Disjoint fun j : ℤ =>
      Set.Ioc (X * Real.exp (-(((j : ℝ) + 1) * L))) (X * Real.exp (-((j : ℝ) * L)))) := by
  intro j j' hjj'
  rw [Function.onFun, Set.disjoint_left]
  intro y hy hy'
  rcases lt_or_gt_of_ne hjj' with h | h
  · have hmono : X * Real.exp (-((j' : ℝ) * L)) ≤ X * Real.exp (-(((j : ℝ) + 1) * L)) := by
      apply mul_le_mul_of_nonneg_left _ hX.le
      rw [Real.exp_le_exp]
      have hcast : ((j : ℝ) + 1) ≤ (j' : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr h)
      nlinarith
    linarith [hy.1, hy'.2]
  · have hmono : X * Real.exp (-((j : ℝ) * L)) ≤ X * Real.exp (-(((j' : ℝ) + 1) * L)) := by
      apply mul_le_mul_of_nonneg_left _ hX.le
      rw [Real.exp_le_exp]
      have hcast : ((j' : ℝ) + 1) ≤ (j : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr h)
      nlinarith
    linarith [hy'.1, hy.2]

/-- Pointwise bound of the damped weight on the multiplicative block `C_j`. -/
lemma hb7s_w_bound {X U' L : ℝ} (hU' : 0 < U') (hUX : U' ≤ X) (hL : 0 < L) (j : ℤ) {y : ℝ}
    (hy1 : X * Real.exp (-(((j : ℝ) + 1) * L)) ≤ y)
    (hy2 : y ≤ X * Real.exp (-((j : ℝ) * L))) :
    Real.exp (-(y / X)) - Real.exp (-(y / U')) ≤
      min 1 (min ((X / U') * Real.exp (-((j : ℝ) * L)))
        (Real.exp (-(Real.exp (-(((j : ℝ) + 1) * L)))))) := by
  have hX : 0 < X := lt_of_lt_of_le hU' hUX
  have hy : 0 < y := lt_of_lt_of_le (by positivity) hy1
  refine le_min ?_ (le_min ?_ ?_)
  · have h1 : Real.exp (-(y / X)) ≤ 1 := Real.exp_le_one_iff.mpr (by have h := div_pos hy hX; linarith)
    have h2 : 0 < Real.exp (-(y / U')) := Real.exp_pos _
    linarith
  · have h1 : Real.exp (-(y / X)) ≤ 1 := Real.exp_le_one_iff.mpr (by have h := div_pos hy hX; linarith)
    have h2 : 1 - y / U' ≤ Real.exp (-(y / U')) := Real.one_sub_le_exp_neg (y / U')
    have h3 : y / U' ≤ (X * Real.exp (-((j : ℝ) * L))) / U' := by
      rw [div_le_div_iff_of_pos_right hU']; exact hy2
    calc Real.exp (-(y / X)) - Real.exp (-(y / U')) ≤ 1 - Real.exp (-(y / U')) := by linarith
      _ ≤ y / U' := by linarith
      _ ≤ (X * Real.exp (-((j : ℝ) * L))) / U' := h3
      _ = (X / U') * Real.exp (-((j : ℝ) * L)) := by ring
  · have h1 : Real.exp (-(y / X)) ≤ Real.exp (-(Real.exp (-(((j : ℝ) + 1) * L)))) := by
      rw [Real.exp_le_exp]
      have h2 : Real.exp (-(((j : ℝ) + 1) * L)) ≤ y / X := by
        rw [le_div_iff₀ hX]
        calc Real.exp (-(((j : ℝ) + 1) * L)) * X = X * Real.exp (-(((j : ℝ) + 1) * L)) := by ring
          _ ≤ y := hy1
      linarith
    have h2 : 0 < Real.exp (-(y / U')) := Real.exp_pos _
    linarith

/-- Nonnegativity of the damped weight for `U' ≤ X`. -/
lemma hb7s_w_nonneg {X U' y : ℝ} (hU' : 0 < U') (hUX : U' ≤ X) (hy : 0 < y) :
    0 ≤ Real.exp (-(y / X)) - Real.exp (-(y / U')) := by
  have hX : 0 < X := lt_of_lt_of_le hU' hUX
  have h1 : (1 : ℝ) / X ≤ 1 / U' := one_div_le_one_div_of_le hU' hUX
  have h2 : y / X ≤ y / U' := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using h1) hy.le
  exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))

/-- `y ↦ y^w` is continuous on the positive reals. -/
lemma hb7s_continuousOn_cpow (w : ℂ) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ w) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun y : ℝ => Complex.exp ((Real.log y : ℂ) * w)) (Set.Ioi 0) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn
        (Real.continuousOn_log.mono (fun y hy => by simpa using hy.ne'))).mul_const w)
  refine hcont.congr (fun y hy => ?_)
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne' : (y : ℂ) ≠ 0)]
  simp only []
  rw [Complex.ofReal_log hy.le]

/-- Continuity of the damped integrand on `(0,∞)`. -/
lemma hb7s_continuousOn_damped {X U' : ℝ} (hX : 0 < X) (hU' : 0 < U')
    {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (z : ι → ℂ) :
    ContinuousOn (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U'))) *
        ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y) (Set.Ioi 0) := by
  have hF : ContinuousOn
      (fun y : ℝ => ∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)) (Set.Ioi 0) :=
    continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (hb7s_continuousOn_cpow _))
  have hG : ContinuousOn
      (fun y : ℝ => ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      (Set.Ioi 0) :=
    (hF.norm.pow 2).div continuousOn_id (fun y hy => hy.ne')
  have h1 : ContinuousOn (fun y : ℝ => Real.exp (-(y / X))) (Set.Ioi 0) :=
    Real.continuous_exp.comp_continuousOn (by fun_prop)
  have h2 : ContinuousOn (fun y : ℝ => Real.exp (-(y / U'))) (Set.Ioi 0) :=
    Real.continuous_exp.comp_continuousOn (by fun_prop)
  have hw : ContinuousOn (fun y : ℝ => Real.exp (-(y / X)) - Real.exp (-(y / U')))
      (Set.Ioi 0) := h1.sub h2
  refine (hw.mul hG).congr (fun y hy => ?_)
  exact mul_div_assoc _ _ _

/-! **Damped mean value bound, the class of small exponents.**  For every `C₀ ≥ 1` there is `K`
such that whenever `L ≥ 1`, `0 < X`, `1 ≤ U'`, `2U' ≤ X`, `log (X/U') ≤ C₀ L`, the frequencies
`γ` are `1/L`-separated and the exponents satisfy `0 ≤ a i ≤ 1/L`,

`∫_{y>0} (e^{-y/X}-e^{-y/U'}) ‖Σ_i z_i y^{a_i - iγ_i}‖² dy/y ≤ K C₀ L Σ_i X^{2a_i} ‖z_i‖²`.

Route: identical freezing argument as `HB7DampedClassBound` but with freezing scale `η = L`
(i.e. `A = 1/L ≥ a_i`); there the per-interval cost is `η + C L ≤ 2CL`, and the sum over
intervals is limited by the weight `h(u) ≤ min(1, (X/U') e^{-u})`, which is non-negligible only
on an interval of length `log (X/U') + O(1)`, i.e. on `O(1 + log(X/U')/η) = O(C₀)` intervals;
the extra factor `C₀ ≥ 1` absorbs it. -/
theorem pls_smallClassBound {C : ℝ} (hC : 0 < C) (hMVT : Work.ZeroDensity.LogFree.MvtMul C) :
    ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ K : ℝ, 0 < K ∧
      ∀ (L X U' : ℝ), 1 ≤ L → 0 < X → 1 ≤ U' → 2 * U' ≤ X → Real.log (X / U') ≤ C₀ * L →
      ∀ {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (z : ι → ℂ),
        (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1 / L) →
        (∀ i j, i ≠ j → 1 / L ≤ |γ i - γ j|) →
        (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U')))
            * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
          ≤ K * C₀ * L * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2 := by
  intro C₀ hC₀
  obtain ⟨K₁, hK₁, hFr⟩ := pls_freezeBlock hC hMVT
  obtain ⟨K₂, hK₂, hWt⟩ := pls_weightSum
  refine ⟨K₁ * K₂, mul_pos hK₁ hK₂, ?_⟩
  intro L X U' hL hX hU1 hUX hlog ι _ a γ z ha0 haL hsep
  have hLpos : 0 < L := by linarith
  have hU' : 0 < U' := by linarith
  have hUX' : U' ≤ X := by linarith
  have hm2 : 2 ≤ X / U' := by
    rw [le_div_iff₀ hU']; linarith
  let F : ℝ → ℂ := fun y => ∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)
  let Ps : ℤ → ℝ := fun j => min 1 (min ((X / U') * Real.exp (-((j : ℝ) * L)))
      (Real.exp (-(Real.exp (-(((j : ℝ) + 1) * L))))))
  let blk : ℤ → Set ℝ := fun j => Set.Ioc (X * Real.exp (-(((j : ℝ) + 1) * L)))
      (X * Real.exp (-((j : ℝ) * L)))
  let B : ℤ → ℝ := fun j =>
      Ps j * (K₁ * L * ∑ i, ‖z i‖ ^ 2 * (X * Real.exp (-((j : ℝ) * L))) ^ (2 * a i))
  change (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y)
      ≤ K₁ * K₂ * C₀ * L * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2
  -- integrability and continuity
  have hInt : IntegrableOn (fun y : ℝ =>
      (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y) (Set.Ioi (0 : ℝ)) := by
    change IntegrableOn (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U')))
      * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      (Set.Ioi (0 : ℝ))
    exact Work.ZeroDensity.LogFree.HB7DampedSmallIntegrable hX hU' hUX' hL a γ z ha0 haL
  have hFs : ContinuousOn
      (fun y : ℝ => ∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)) (Set.Ioi 0) :=
    continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (hb7s_continuousOn_cpow _))
  have hG : ContinuousOn (fun y : ℝ => ‖F y‖ ^ 2 / y) (Set.Ioi 0) :=
    (hFs.norm.pow 2).div continuousOn_id (fun y hy => hy.ne')
  have hcontt : ContinuousOn (fun y : ℝ =>
      (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y) (Set.Ioi 0) :=
    hb7s_continuousOn_damped hX hU' a γ z
  -- block decomposition
  have huni : (⋃ j : ℤ, blk j) = Set.Ioi (0 : ℝ) := hb7s_iUnion_blk hX hLpos
  have hdisj : Pairwise (Function.onFun Disjoint blk) := hb7s_pairwiseDisjoint_blk hX hLpos
  have hdecomp : (∫ y in Set.Ioi (0 : ℝ),
        (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y)
      = ∑' j : ℤ, ∫ y in blk j,
          (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y := by
    rw [← huni]
    exact MeasureTheory.integral_iUnion (fun j => measurableSet_Ioc) hdisj (by rw [huni]; exact hInt)
  -- per-block bound
  have hblk : ∀ j : ℤ, (∫ y in blk j,
        (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y) ≤ B j := by
    intro j
    have hBval : B j = Ps j * (K₁ * L * ∑ i, ‖z i‖ ^ 2
        * (X * Real.exp (-((j : ℝ) * L))) ^ (2 * a i)) := rfl
    rw [hBval]
    have hYpos : 0 < X * Real.exp (-((j : ℝ) * L)) := by positivity
    have hle : X * Real.exp (-((j : ℝ) * L)) * Real.exp (-L) ≤ X * Real.exp (-((j : ℝ) * L)) := by
      have h1 : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [hYpos]
    have hleft : X * Real.exp (-(((j : ℝ) + 1) * L))
        = X * Real.exp (-((j : ℝ) * L)) * Real.exp (-L) := by
      have he : -(((j : ℝ) + 1) * L) = -((j : ℝ) * L) + (-L) := by ring
      rw [he, Real.exp_add]; ring
    have hblkY : blk j = Set.Ioc (X * Real.exp (-((j : ℝ) * L)) * Real.exp (-L))
        (X * Real.exp (-((j : ℝ) * L))) := by
      show Set.Ioc (X * Real.exp (-(((j : ℝ) + 1) * L))) (X * Real.exp (-((j : ℝ) * L))) = _
      rw [hleft]
    rw [hblkY, ← intervalIntegral.integral_of_le hle]
    have hsub : Set.uIcc (X * Real.exp (-((j : ℝ) * L)) * Real.exp (-L))
        (X * Real.exp (-((j : ℝ) * L))) ⊆ Set.Ioi (0 : ℝ) := by
      intro y hy
      rw [Set.uIcc_of_le hle] at hy
      exact lt_of_lt_of_le (by positivity) hy.1
    have hmono : (∫ y in (X * Real.exp (-((j : ℝ) * L)) * Real.exp (-L))..
          (X * Real.exp (-((j : ℝ) * L))),
          (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y)
        ≤ ∫ y in (X * Real.exp (-((j : ℝ) * L)) * Real.exp (-L))..
          (X * Real.exp (-((j : ℝ) * L))), Ps j * (‖F y‖ ^ 2 / y) := by
      refine intervalIntegral.integral_mono_on hle ?_ ?_ ?_
      · exact ContinuousOn.intervalIntegrable (hcontt.mono hsub)
      · exact ContinuousOn.intervalIntegrable ((continuousOn_const.mul hG).mono hsub)
      · intro y hy
        have hypos : 0 < y := lt_of_lt_of_le (mul_pos hYpos (Real.exp_pos (-L))) hy.1
        rw [mul_div_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (by positivity) hypos.le)
        have hy1' : X * Real.exp (-(((j : ℝ) + 1) * L)) ≤ y := by rw [hleft]; exact hy.1
        exact hb7s_w_bound hU' hUX' hLpos j hy1' hy.2
    calc (∫ y in (X * Real.exp (-((j : ℝ) * L)) * Real.exp (-L))..
            (X * Real.exp (-((j : ℝ) * L))),
            (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y)
        ≤ _ := hmono
      _ = Ps j * (∫ y in (X * Real.exp (-((j : ℝ) * L)) * Real.exp (-L))..
            (X * Real.exp (-((j : ℝ) * L))), ‖F y‖ ^ 2 / y) := by
          rw [intervalIntegral.integral_const_mul]
      _ ≤ Ps j * (K₁ * L * ∑ i, ‖z i‖ ^ 2 * (X * Real.exp (-((j : ℝ) * L))) ^ (2 * a i)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (le_min (by norm_num) (le_min (by positivity) (by positivity)))
          exact hFr L hL a γ z (X * Real.exp (-((j : ℝ) * L))) hYpos ha0 haL hsep
  -- summability of the bound family
  have hgnn : ∀ i : ι, ∀ j : ℤ, 0 ≤ (K₁ * L * (X ^ (2 * a i) * ‖z i‖ ^ 2))
      * (Ps j * Real.exp (-(2 * a i * ((j : ℝ) * L)))) := by
    intro i j
    refine mul_nonneg (mul_nonneg (mul_nonneg hK₁.le hLpos.le)
      (mul_nonneg (Real.rpow_nonneg hX.le _) (sq_nonneg _))) ?_
    exact mul_nonneg (le_min (by norm_num) (le_min (by positivity) (by positivity)))
      (Real.exp_pos _).le
  have hgs : ∀ i : ι, Summable (fun j : ℤ => (K₁ * L * (X ^ (2 * a i) * ‖z i‖ ^ 2))
      * (Ps j * Real.exp (-(2 * a i * ((j : ℝ) * L))))) := by
    intro i
    exact (hWt (X / U') C₀ L (a i) hm2 hC₀ hL hlog (ha0 i) (haL i)).1.mul_left _
  have hrew : ∀ j : ℤ, B j = ∑ i : ι, (K₁ * L * (X ^ (2 * a i) * ‖z i‖ ^ 2))
      * (Ps j * Real.exp (-(2 * a i * ((j : ℝ) * L)))) := by
    intro j
    have h1 : ∀ i : ι, (X * Real.exp (-((j : ℝ) * L))) ^ (2 * a i)
        = X ^ (2 * a i) * Real.exp (-(2 * a i * ((j : ℝ) * L))) := by
      intro i
      rw [Real.mul_rpow hX.le (Real.exp_nonneg _), ← Real.exp_mul]
      congr 1
      ring_nf
    simp only [B, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h1 i]
    ring_nf
  have hBsummable : Summable B := by
    rw [show B = fun j : ℤ => ∑ i : ι, (K₁ * L * (X ^ (2 * a i) * ‖z i‖ ^ 2))
        * (Ps j * Real.exp (-(2 * a i * ((j : ℝ) * L)))) from funext hrew]
    exact (hb7s_tsum_finset_sum_of_nonneg (Finset.univ : Finset ι)
      (fun i _ => hgnn i) (fun i _ => hgs i)).1
  have hAnn : ∀ j : ℤ, 0 ≤ ∫ y in blk j,
      (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y := by
    intro j
    refine setIntegral_nonneg (measurableSet_Ioc) (fun y hy => ?_)
    have hypos : 0 < y := lt_trans (by positivity) hy.1
    rw [mul_div_assoc]
    exact mul_nonneg (hb7s_w_nonneg hU' hUX' hypos) (div_nonneg (by positivity) hypos.le)
  have hAsummable : Summable (fun j : ℤ => ∫ y in blk j,
      (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y) :=
    Summable.of_nonneg_of_le hAnn hblk hBsummable
  have hstep2 : (∑' j : ℤ, ∫ y in blk j,
        (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y) ≤ ∑' j : ℤ, B j :=
    Summable.tsum_le_tsum hblk hAsummable hBsummable
  -- evaluate the block sum
  have hBsum : (∑' j : ℤ, B j)
      ≤ K₁ * L * (K₂ * C₀) * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2 := by
    rw [show (∑' j : ℤ, B j) = ∑' j : ℤ, ∑ i : ι, (K₁ * L * (X ^ (2 * a i) * ‖z i‖ ^ 2))
        * (Ps j * Real.exp (-(2 * a i * ((j : ℝ) * L)))) from by rw [funext hrew]]
    rw [(hb7s_tsum_finset_sum_of_nonneg (Finset.univ : Finset ι)
      (fun i _ => hgnn i) (fun i _ => hgs i)).2]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [tsum_mul_left]
    calc (K₁ * L * (X ^ (2 * a i) * ‖z i‖ ^ 2))
          * (∑' j : ℤ, Ps j * Real.exp (-(2 * a i * ((j : ℝ) * L))))
        ≤ (K₁ * L * (X ^ (2 * a i) * ‖z i‖ ^ 2)) * (K₂ * C₀) := by
          refine mul_le_mul_of_nonneg_left
            (hWt (X / U') C₀ L (a i) hm2 hC₀ hL hlog (ha0 i) (haL i)).2 ?_
          exact mul_nonneg (mul_nonneg hK₁.le hLpos.le)
            (mul_nonneg (Real.rpow_nonneg hX.le _) (sq_nonneg _))
      _ = K₁ * L * (K₂ * C₀) * (X ^ (2 * a i) * ‖z i‖ ^ 2) := by ring
  calc (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y)
      = ∑' j : ℤ, ∫ y in blk j,
          (Real.exp (-(y / X)) - Real.exp (-(y / U'))) * ‖F y‖ ^ 2 / y := hdecomp
    _ ≤ ∑' j : ℤ, B j := hstep2
    _ ≤ K₁ * L * (K₂ * C₀) * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2 := hBsum
    _ = K₁ * K₂ * C₀ * L * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2 := by ring

/-! ## The pole Gram form as a damped mean square -/

/-- Integrability of the pole-Gram pair kernel `(e^{-y/X}-e^{-y/U'}) y^{w-1}` in the shape of the
integrand of `poleK`, for `w = 2 - ρ - \barσ` with `Re w > 0`. -/
private lemma pls_pairIntegrable {X U' : ℝ} (hX : 0 < X) (hU' : 0 < U') {ρ σ : ℂ}
    (hρ : ρ.re < 1) (hσ : σ.re < 1) :
    IntegrableOn (fun y : ℝ => ((Real.exp (-(y / X)) - Real.exp (-(y / U')) : ℝ) : ℂ)
        * (y : ℂ) ^ (1 - ρ) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - σ)) / (y : ℂ)) (Set.Ioi 0) := by
  have hw : 0 < (2 - ρ - (starRingEnd ℂ) σ).re := by
    have h : (2 - ρ - (starRingEnd ℂ) σ).re = 2 - ρ.re - σ.re := by
      simp [Complex.sub_re, Complex.conj_re]
    rw [h]; linarith
  have h := Work.ZeroDensity.HB7PoleGramIntegrable hX hU' hw
  refine h.congr_fun ?_ measurableSet_Ioi
  intro y hy
  have h1 := Work.ZeroDensity.hb7PoleK_cpow_mul_conj_cpow_div hy ρ σ
  calc ((Real.exp (-(y / X)) - Real.exp (-(y / U')) : ℝ) : ℂ)
        * (y : ℂ) ^ ((2 - ρ - (starRingEnd ℂ) σ) - 1)
      = ((Real.exp (-(y / X)) - Real.exp (-(y / U')) : ℝ) : ℂ)
        * ((y : ℂ) ^ (1 - ρ) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - σ)) / (y : ℂ)) := by
        rw [← h1]
    _ = ((Real.exp (-(y / X)) - Real.exp (-(y / U')) : ℝ) : ℂ)
        * (y : ℂ) ^ (1 - ρ) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - σ)) / (y : ℂ) := by ring

/-- The real part of an integral is the integral of the real part. -/
private lemma pls_integral_re (f : ℝ → ℂ)
    (hf : Integrable f (volume.restrict (Set.Ioi (0 : ℝ)))) :
    (∫ y in Set.Ioi (0 : ℝ), (f y).re) = (∫ y in Set.Ioi (0 : ℝ), f y).re := by
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM hf
  simpa [Complex.reCLM_apply] using h

/-- `∫` of a finite sum of complex-valued functions over `(0,∞)`. -/
private lemma pls_integral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, Integrable (f i) (volume.restrict (Set.Ioi (0 : ℝ)))) :
    (∫ y in Set.Ioi (0 : ℝ), ∑ i ∈ s, f i y) = ∑ i ∈ s, ∫ y in Set.Ioi (0 : ℝ), f i y :=
  integral_finsetSum s h

/-- **The pole Gram quadratic form is a damped mean square**: for `0 < U' ≤ X` and
`(ρ i).re < 1`,
`(Σ_{i,j} z_i \bar z_j K_ij).re = ∫_{y>0} (e^{-y/X} - e^{-y/U'}) ‖Σ_i z_i y^{1-ρ_i}‖² dy/y`. -/
theorem pls_poleGramReIntegral {X U' : ℝ} (hX : 0 < X) (hU' : 0 < U') (hUX : U' ≤ X)
    (m : ℕ) (ρ : Fin m → ℂ) (hρ : ∀ i, (ρ i).re < 1) (z : Fin m → ℂ) :
    (poleGram m X U' ρ z).re
      = ∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U')))
          * ‖∑ i, z i * (y : ℂ) ^ (1 - ρ i)‖ ^ 2 / y := by
  classical
  set F : Fin m → Fin m → ℝ → ℂ := fun i j y =>
      ((Real.exp (-(y / X)) - Real.exp (-(y / U')) : ℝ) : ℂ)
        * (y : ℂ) ^ (1 - ρ i) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - ρ j)) / (y : ℂ) with hFdef
  set Φ : ℝ → ℂ := fun y =>
      ((Real.exp (-(y / X)) - Real.exp (-(y / U')) : ℝ) : ℂ)
        * (∑ i, z i * (y : ℂ) ^ (1 - ρ i))
        * (starRingEnd ℂ) (∑ i, z i * (y : ℂ) ^ (1 - ρ i)) / (y : ℂ) with hΦdef
  -- each entry is the integral of the pair kernel
  have hK : ∀ i j : Fin m, poleK X U' (ρ i) (ρ j) = ∫ y in Set.Ioi (0 : ℝ), F i j y := by
    intro i j
    exact Work.ZeroDensity.HB7PoleKIntegral hX hU' hUX (ρ i) (ρ j) (hρ i) (hρ j)
  have hFint : ∀ i j : Fin m, Integrable (F i j) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro i j
    exact pls_pairIntegrable hX hU' (hρ i) (hρ j)
  have hcF : ∀ i j : Fin m,
      Integrable (fun y => (z i * (starRingEnd ℂ) (z j)) * F i j y)
        (volume.restrict (Set.Ioi (0 : ℝ))) := fun i j => (hFint i j).const_mul _
  -- the quadratic form as a double sum of integrated pair kernels
  have hsum_eq : (∑ i, ∑ j, z i * (starRingEnd ℂ) (z j) * poleK X U' (ρ i) (ρ j))
      = ∑ i, ∑ j, ∫ y in Set.Ioi (0 : ℝ), (z i * (starRingEnd ℂ) (z j)) * F i j y := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hK i j, ← integral_const_mul]
  have hInt2 : ∀ i : Fin m,
      Integrable (fun y => ∑ j, (z i * (starRingEnd ℂ) (z j)) * F i j y)
        (volume.restrict (Set.Ioi (0 : ℝ))) := fun i => integrable_finsetSum _ (fun j _ => hcF i j)
  have hInt3 : Integrable (fun y => ∑ i, ∑ j, (z i * (starRingEnd ℂ) (z j)) * F i j y)
      (volume.restrict (Set.Ioi (0 : ℝ))) := integrable_finsetSum _ (fun i _ => hInt2 i)
  -- interchange the finite double sum with the integral
  have hint_eq : (∑ i, ∑ j, ∫ y in Set.Ioi (0 : ℝ), (z i * (starRingEnd ℂ) (z j)) * F i j y)
      = ∫ y in Set.Ioi (0 : ℝ), ∑ i, ∑ j, (z i * (starRingEnd ℂ) (z j)) * F i j y := by
    rw [pls_integral_finset_sum (Finset.univ : Finset (Fin m))
      (f := fun i y => ∑ j, (z i * (starRingEnd ℂ) (z j)) * F i j y) (fun i _ => hInt2 i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pls_integral_finset_sum (Finset.univ : Finset (Fin m))
      (f := fun j y => (z i * (starRingEnd ℂ) (z j)) * F i j y) (fun j _ => hcF i j)]
  -- the pointwise algebraic identification
  have hpoint : (∫ y in Set.Ioi (0 : ℝ), ∑ i, ∑ j, (z i * (starRingEnd ℂ) (z j)) * F i j y)
      = ∫ y in Set.Ioi (0 : ℝ), Φ y := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    exact Work.ZeroDensity.HB7PoleGramDoubleSum m ρ z
      (Real.exp (-(y / X)) - Real.exp (-(y / U'))) y
  have hlast : (∫ y in Set.Ioi (0 : ℝ), (Φ y).re)
      = ∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U')))
          * ‖∑ i, z i * (y : ℂ) ^ (1 - ρ i)‖ ^ 2 / y := by
    rw [hΦdef]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    exact Work.ZeroDensity.HB7PoleGramReId hy (∑ i, z i * (y : ℂ) ^ (1 - ρ i))
  have hIntΦ : Integrable Φ (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine hInt3.congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    exact Work.ZeroDensity.HB7PoleGramDoubleSum m ρ z
      (Real.exp (-(y / X)) - Real.exp (-(y / U'))) y
  rw [poleGram, congrArg Complex.re hsum_eq, hint_eq, hpoint, ← pls_integral_re Φ hIntΦ, hlast]

lemma pls_one_sub (ρ : ℂ) :
    (1 : ℂ) - ρ = ((1 - ρ.re : ℝ) : ℂ) - ((ρ.im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  · simp [Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]

/-- Cauchy–Schwarz for a finite family of complex numbers. -/
lemma pls_norm_sum_sq_le_card {κ : Type*} [Fintype κ] (w : κ → ℂ) :
    ‖∑ k, w k‖ ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ k, ‖w k‖ ^ 2 := by
  have h1 : ‖∑ k, w k‖ ≤ ∑ k, ‖w k‖ := norm_sum_le _ _
  have h2 : ‖∑ k, w k‖ ^ 2 ≤ (∑ k, ‖w k‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (∑ k, ‖w k‖) ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ k, ‖w k‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ)) (f := fun k => ‖w k‖)
    simpa [Finset.card_univ] using this
  linarith

/-- `log₂ x ≤ n ↔ x ≤ 2^n` for `x > 0`. -/
lemma pls_log2_le_iff {x : ℝ} (hx : 0 < x) (n : ℕ) :
    log2 x ≤ (n : ℝ) ↔ x ≤ 2 ^ n := by
  rw [log2, div_le_iff₀ (Real.log_pos one_lt_two)]
  rw [← Real.log_pow]
  exact Real.log_le_log_iff hx (by positivity)

/-- `log₂` is monotone on the positive reals. -/
lemma pls_log2_mono_pos {x y : ℝ} (hx : 0 < x) (h : x ≤ y) :
    log2 x ≤ log2 y := by
  rw [log2, log2]
  have hy : 0 < y := lt_of_lt_of_le hx h
  exact div_le_div_of_nonneg_right (Real.log_le_log hx h) (Real.log_nonneg one_le_two)

/-- `log₂ y ≥ 0` for `y ≥ 1`. -/
lemma pls_log2_nonneg {y : ℝ} (hy : 1 ≤ y) : 0 ≤ log2 y := by
  rw [log2]
  exact div_nonneg (Real.log_nonneg hy) (Real.log_nonneg one_le_two)

/-- The class of an index: if `⌈log₂ (x L)⌉₊ = n`, then `x ≤ 2^n/L`, and
`2^{n-1}/L < x` when `n ≥ 1`. -/
lemma pls_class_facts {x L : ℝ} (hx : 0 ≤ x) (hL : 0 < L) {n : ℕ}
    (h : ⌈log2 (x * L)⌉₊ = n) :
    x ≤ 2 ^ n / L ∧ (0 < n → 2 ^ (n - 1) / L < x) := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · subst hx0
    have hlog : log2 ((0 : ℝ) * L) = 0 := by
      rw [log2, zero_mul, Real.log_zero, zero_div]
    rw [hlog, Nat.ceil_zero] at h
    subst h
    refine ⟨?_, fun hn => absurd hn (lt_irrefl 0)⟩
    rw [pow_zero]
    positivity
  · have hxL : 0 < x * L := mul_pos hxpos hL
    have hle : log2 (x * L) ≤ (n : ℝ) :=
      Nat.ceil_le.mp (le_of_eq h)
    have hxn : x * L ≤ 2 ^ n := (pls_log2_le_iff hxL n).mp hle
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hL]
      exact hxn
    · intro hn
      have hlt : ((n - 1 : ℕ) : ℝ) < log2 (x * L) := by
        apply Nat.lt_ceil.mp
        rw [h]
        omega
      have hpow : 2 ^ (n - 1) < x * L := by
        by_contra hcon
        push Not at hcon
        have := (pls_log2_le_iff hxL (n - 1)).mpr hcon
        linarith
      rw [div_lt_iff₀ hL]
      exact hpow

/-- Cauchy–Schwarz over the classes, performed inside the integral. -/
lemma pls_integral_class_split
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (cl : ι → κ) {X U : ℝ} (hX : 0 < X) (hU : 0 < U) (hUX : U ≤ X)
    (a g : ι → ℝ) (z : ι → ℂ)
    (hInt : ∀ k : κ, IntegrableOn (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i : {i : ι // cl i = k}, z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y)
      (Set.Ioi (0 : ℝ))) :
    (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y)
      ≤ (Fintype.card κ : ℝ) * ∑ k : κ, ∫ y in Set.Ioi (0 : ℝ),
          (Real.exp (-(y / X)) - Real.exp (-(y / U)))
            * ‖∑ i : {i : ι // cl i = k}, z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y := by
  have hg0 : ∀ y : ℝ, 0 < y → 0 ≤ Real.exp (-(y / X)) - Real.exp (-(y / U)) := by
    intro y hy
    have h1 : (1 : ℝ) / X ≤ 1 / U := one_div_le_one_div_of_le hU hUX
    have h2 : y / X ≤ y / U := by
      rw [div_eq_mul_one_div y X, div_eq_mul_one_div y U]
      exact mul_le_mul_of_nonneg_left h1 hy.le
    have h3 : -(y / U) ≤ -(y / X) := by linarith
    have h4 := Real.exp_le_exp.mpr h3
    linarith
  have hfib : ∀ y : ℝ, (∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I))
      = ∑ k : κ, ∑ i : {i : ι // cl i = k},
          z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I) := fun y =>
    (Fintype.sum_fiberwise cl
      (fun i => z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I))).symm
  have hpoint : ∀ᵐ y ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y
      ≤ (Fintype.card κ : ℝ) * ∑ k : κ, (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i : {i : ι // cl i = k},
            z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    have hcs := pls_norm_sum_sq_le_card (κ := κ)
      (w := fun k => ∑ i : {i : ι // cl i = k},
        z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I))
    rw [hfib y]
    calc (Real.exp (-(y / X)) - Real.exp (-(y / U)))
          * ‖∑ k : κ, ∑ i : {i : ι // cl i = k},
              z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y
        = ((Real.exp (-(y / X)) - Real.exp (-(y / U))) / y)
          * ‖∑ k : κ, ∑ i : {i : ι // cl i = k},
              z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 := by ring
      _ ≤ ((Real.exp (-(y / X)) - Real.exp (-(y / U))) / y)
          * ((Fintype.card κ : ℝ) * ∑ k : κ, ‖∑ i : {i : ι // cl i = k},
              z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (div_nonneg (hg0 y hy0) hy0.le)
      _ = (Fintype.card κ : ℝ) * ∑ k : κ, (Real.exp (-(y / X)) - Real.exp (-(y / U)))
          * ‖∑ i : {i : ι // cl i = k},
              z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
  have hInt2 : Integrable (fun y : ℝ => (Fintype.card κ : ℝ) * ∑ k : κ,
        (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i : {i : ι // cl i = k},
            z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun k _ => hInt k)
  have hmono : (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y)
      ≤ (∫ y in Set.Ioi (0 : ℝ), (Fintype.card κ : ℝ) * ∑ k : κ,
          (Real.exp (-(y / X)) - Real.exp (-(y / U)))
          * ‖∑ i : {i : ι // cl i = k},
              z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y) := by
    apply integral_mono_of_nonneg
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
      exact div_nonneg (mul_nonneg (hg0 y hy) (sq_nonneg _)) hy.le
    · exact hInt2
    · filter_upwards [hpoint] with y hy
      exact hy
  calc (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y)
      ≤ (∫ y in Set.Ioi (0 : ℝ), (Fintype.card κ : ℝ) * ∑ k : κ,
          (Real.exp (-(y / X)) - Real.exp (-(y / U)))
          * ‖∑ i : {i : ι // cl i = k},
              z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y) := hmono
    _ = (Fintype.card κ : ℝ) * ∑ k : κ, ∫ y in Set.Ioi (0 : ℝ),
          (Real.exp (-(y / X)) - Real.exp (-(y / U)))
          * ‖∑ i : {i : ι // cl i = k},
              z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y := by
        rw [integral_const_mul]
        congr 1
        rw [integral_finsetSum _ (fun k _ => hInt k)]


/-- **L4**: the damped large sieve for the pole Gram matrix of a system of zeros with
`1/𝓛`-separated imaginary parts (`𝓛 = log (q(T+2))`). -/
theorem poleLargeSieve (p : Work.ZeroDensity.LogFree.Params) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T σ : ℝ), 1 ≤ T → D₀ ≤ Work.ZeroDensity.LogFree.scale q T →
      p.σ₀ ≤ σ → σ ≤ 1 →
      ∀ (m : ℕ) (ρ : Fin m → ℂ) (z : Fin m → ℂ),
        (∀ i, σ ≤ (ρ i).re) → (∀ i, (ρ i).re < 1) → (∀ i, |(ρ i).im| ≤ T) →
        (∀ i j, i ≠ j → 1 / Work.ZeroDensity.LogFree.Lscale q T ≤ |(ρ i).im - (ρ j).im|) →
        (Work.ZeroDensity.LogFree.poleGram m (Work.ZeroDensity.LogFree.Dpow q T p.x)
            (Work.ZeroDensity.LogFree.Dpow q T p.u / (Work.ZeroDensity.LogFree.Lscale q T) ^ 2)
            ρ z).re
          ≤ C_K * (2 + Work.ZeroDensity.LogFree.log2 (1 + (1 - σ) * Work.ZeroDensity.LogFree.Lscale q T))
              * Work.ZeroDensity.LogFree.Lscale q T
              * Work.ZeroDensity.LogFree.Dpow q T (2 * p.x * (1 - σ)) * ∑ i, ‖z i‖ ^ 2 := by
  obtain ⟨Cm, hCmpos, hMVT⟩ := Work.ZeroDensity.HB7MvtMul
  obtain ⟨K₁, hK₁pos, hK₁⟩ := HB7DampedClassBound hCmpos hMVT
  set C₀ : ℝ := p.x - p.u + 2 with hC₀def
  have hC₀ge : 1 ≤ C₀ := by
    have huv : p.u < p.x := lt_trans p.huv p.hvx
    rw [hC₀def]
    linarith
  obtain ⟨K₂, hK₂pos, hK₂⟩ := pls_smallClassBound hCmpos hMVT C₀ hC₀ge
  obtain ⟨Dreg, hDregpos, hDreg⟩ := HB7ParamsRegime p
  refine ⟨2 * max K₁ (K₂ * C₀), by positivity, Dreg, hDregpos, ?_⟩
  intro q hq _inst T σ hT hDq hσ0 hσ1 m ρ z hσre hρ1 him hsep
  set L : ℝ := Lscale q T with hLdef
  set X : ℝ := Dpow q T p.x with hXdef
  set U : ℝ := Dpow q T p.u / L ^ 2 with hUdef
  obtain ⟨hL1, hXpos, hU1, h2UX, hlog⟩ := hDreg q hq T hT hDq
  rw [← hLdef] at hL1 hU1 h2UX hlog
  rw [← hUdef] at hU1 h2UX hlog
  rw [← hXdef] at hXpos h2UX hlog
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU1
  have hUX : U ≤ X := by linarith
  have hxpos : 0 < p.x := lt_trans p.hw (lt_trans p.hwu (lt_trans p.huv p.hvx))
  have hscale1 : (1 : ℝ) ≤ scale q T := by
    rw [scale]
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hscale0 : 0 < scale q T := lt_of_lt_of_le zero_lt_one hscale1
  have hX1 : 1 ≤ X := by
    rw [hXdef, Dpow]
    exact Real.one_le_rpow hscale1 hxpos.le
  -- exponents of the pole factor
  set a : Fin m → ℝ := fun i => 1 - (ρ i).re with hadef
  set g : Fin m → ℝ := fun i => (ρ i).im with hgdef
  have hexp : ∀ i, (1 : ℂ) - ρ i = ((a i : ℂ) - ((g i : ℂ)) * Complex.I) := by
    intro i
    rw [hadef, hgdef]
    exact pls_one_sub (ρ i)
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i
    rw [hadef]; simp only
    linarith [hρ1 i]
  have ha1 : ∀ i, a i ≤ 1 := by
    intro i
    rw [hadef]; simp only
    have h := le_trans (le_trans p.hσ₀.le hσ0) (hσre i)
    linarith
  have ha_le : ∀ i, a i ≤ 1 - σ := by
    intro i
    rw [hadef]; simp only
    linarith [hσre i]
  have ha_half : ∀ i, a i < 1 / 2 := by
    intro i
    rw [hadef]; simp only
    have h := lt_of_lt_of_le p.hσ₀ (le_trans hσ0 (hσre i))
    linarith
  have hsep' : ∀ i j, i ≠ j → 1 / L ≤ |g i - g j| := by
    intro i j hij
    simpa [hgdef] using hsep i j hij
  -- the pole Gram form as an integral
  have hgram : (poleGram m X U ρ z).re
      = ∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
          * ‖∑ i, z i * (y : ℂ) ^ (1 - ρ i)‖ ^ 2 / y :=
    pls_poleGramReIntegral hXpos hUpos hUX m ρ hρ1 z
  have hrewrite : (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i, z i * (y : ℂ) ^ (1 - ρ i)‖ ^ 2 / y)
      = (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hsum : (∑ i, z i * (y : ℂ) ^ (1 - ρ i))
        = ∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hexp i]
    simp only [hsum]
  -- the class decomposition
  set K : ℕ := ⌈log2 (1 + (1 - σ) * L)⌉₊ with hKdef
  have hlog2nn : 0 ≤ log2 (1 + (1 - σ) * L) := by
    apply pls_log2_nonneg
    have : 0 ≤ (1 - σ) * L := mul_nonneg (by linarith) hLpos.le
    linarith
  have hclle : ∀ i, ⌈log2 (a i * L)⌉₊ ≤ K := by
    intro i
    rcases eq_or_lt_of_le (ha0 i) with h0 | hpos
    · rw [← h0, zero_mul, log2, Real.log_zero, zero_div, Nat.ceil_zero, hKdef]
      exact Nat.zero_le _
    · rw [hKdef]
      refine Nat.ceil_le.mpr (le_trans ?_ (Nat.ceil_le.mp le_rfl))
      exact pls_log2_mono_pos (mul_pos hpos hLpos)
        (by nlinarith [hLpos.le, ha_le i, ha0 i])
  set cl : Fin m → Fin (K + 1) :=
    fun i => ⟨⌈log2 (a i * L)⌉₊, Nat.lt_succ_of_le (hclle i)⟩ with hcldef
  have hclval : ∀ i, (cl i).val = ⌈log2 (a i * L)⌉₊ := by
    intro i
    simp [hcldef]
  have hkfacts : ∀ (k : Fin (K + 1)) (i : Fin m), cl i = k →
      a i ≤ 2 ^ k.val / L ∧ (0 < k.val → 2 ^ (k.val - 1) / L < a i) := by
    intro k i hi
    have hceil : ⌈log2 (a i * L)⌉₊ = k.val := by rw [← hclval i, hi]
    exact pls_class_facts (ha0 i) hLpos hceil
  -- integrability of the class integrands
  have hInteg : ∀ k : Fin (K + 1), IntegrableOn (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i : {i : Fin m // cl i = k},
            z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y) (Set.Ioi (0 : ℝ)) := by
    intro k
    exact Work.ZeroDensity.LogFree.HB7DampedSmallIntegrable hXpos hUpos hUX le_rfl
      (fun i : {i : Fin m // cl i = k} => a i.1) (fun i => g i.1) (fun i => z i.1)
      (fun i => ha0 i.1) (fun i => by simpa using ha1 i.1)
  -- the mean value bound for each class
  have hclass : ∀ k : Fin (K + 1), (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i : {i : Fin m // cl i = k},
            z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y)
      ≤ max K₁ (K₂ * C₀) * L * X ^ (2 * (1 - σ)) * ∑ i : {i : Fin m // cl i = k}, ‖z i‖ ^ 2 := by
    intro k
    by_cases hne : Nonempty {i : Fin m // cl i = k}
    · obtain ⟨i₀⟩ := hne
      rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
      · have ha_small : ∀ i : {i : Fin m // cl i = k}, a i ≤ 1 / L := by
          intro i
          have h1 := (hkfacts k i.1 i.2).1
          rw [hk0, pow_zero] at h1
          simpa using h1
        have hb := hK₂ L X U hL1 hXpos hU1 h2UX hlog (fun i : {i : Fin m // cl i = k} => a i)
          (fun i : {i : Fin m // cl i = k} => g i.1) (fun i => z i.1) (fun i => ha0 i.1) ha_small
          (fun i j hij => hsep' i.1 j.1 (fun h => hij (Subtype.ext h)))
        calc (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
              * ‖∑ i : {i : Fin m // cl i = k},
                  z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y)
            ≤ K₂ * C₀ * L * ∑ i : {i : Fin m // cl i = k}, X ^ (2 * a i) * ‖z i‖ ^ 2 := hb
          _ ≤ K₂ * C₀ * L * (X ^ (2 * (1 - σ)) * ∑ i : {i : Fin m // cl i = k}, ‖z i‖ ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [Finset.mul_sum]
              apply Finset.sum_le_sum
              intro i _
              exact mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith [ha_le i])) (sq_nonneg _)
          _ = K₂ * C₀ * L * X ^ (2 * (1 - σ)) * ∑ i : {i : Fin m // cl i = k}, ‖z i‖ ^ 2 := by ring
          _ ≤ max K₁ (K₂ * C₀) * L * X ^ (2 * (1 - σ))
                * ∑ i : {i : Fin m // cl i = k}, ‖z i‖ ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun i _ => sq_nonneg _))
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXpos.le _)
              apply mul_le_mul_of_nonneg_right (le_max_right K₁ (K₂ * C₀)) hLpos.le
      · have hlow : (2 : ℝ) ^ (k.val - 1) / L < a i₀.1 := (hkfacts k i₀.1 i₀.2).2 hkpos
        have hpow : (2 : ℝ) ^ k.val = 2 * 2 ^ (k.val - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hkpos]
          rw [pow_succ']
        have hAinv : 1 / L ≤ (2 : ℝ) ^ k.val / L := by
          apply div_le_div_of_nonneg_right _ hLpos.le
          exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
        have hA1 : (2 : ℝ) ^ k.val / L ≤ 1 := by
          have h2 : (2 : ℝ) ^ (k.val - 1) < L / 2 := by
            rw [div_lt_iff₀ hLpos] at hlow
            have hhalf : a i₀.1 < 1 / 2 := ha_half i₀.1
            nlinarith
          have : (2 : ℝ) ^ k.val < L := by rw [hpow]; linarith
          rw [div_le_one hLpos]
          exact this.le
        have hA2 : (2 : ℝ) ^ k.val / L / 2 = (2 : ℝ) ^ (k.val - 1) / L := by
          rw [hpow]; field_simp
        have ha_lo : ∀ i : {i : Fin m // cl i = k}, (2 : ℝ) ^ k.val / L / 2 ≤ a i := by
          intro i
          have h := (hkfacts k i.1 i.2).2 hkpos
          rw [hA2]
          exact h.le
        have ha_hi : ∀ i : {i : Fin m // cl i = k}, a i ≤ (2 : ℝ) ^ k.val / L :=
          fun i => (hkfacts k i.1 i.2).1
        have hb := hK₁ L ((2 : ℝ) ^ k.val / L) X U hL1 hAinv hA1 hXpos hU1 h2UX
          (fun i : {i : Fin m // cl i = k} => a i) (fun i : {i : Fin m // cl i = k} => g i.1)
          (fun i => z i.1) ha_lo ha_hi (fun i j hij => hsep' i.1 j.1 (fun h => hij (Subtype.ext h)))
        calc (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
              * ‖∑ i : {i : Fin m // cl i = k},
                  z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y)
            ≤ K₁ * L * ∑ i : {i : Fin m // cl i = k}, X ^ (2 * a i) * ‖z i‖ ^ 2 := hb
          _ ≤ K₁ * L * (X ^ (2 * (1 - σ)) * ∑ i : {i : Fin m // cl i = k}, ‖z i‖ ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [Finset.mul_sum]
              apply Finset.sum_le_sum
              intro i _
              exact mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith [ha_le i])) (sq_nonneg _)
          _ = K₁ * L * X ^ (2 * (1 - σ)) * ∑ i : {i : Fin m // cl i = k}, ‖z i‖ ^ 2 := by ring
          _ ≤ max K₁ (K₂ * C₀) * L * X ^ (2 * (1 - σ))
                * ∑ i : {i : Fin m // cl i = k}, ‖z i‖ ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun i _ => sq_nonneg _))
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXpos.le _)
              apply mul_le_mul_of_nonneg_right (le_max_left K₁ (K₂ * C₀)) hLpos.le
    · haveI : IsEmpty {i : Fin m // cl i = k} := ⟨fun x => hne ⟨x⟩⟩
      have hzero : (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
          * ‖∑ i : {i : Fin m // cl i = k},
              z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y) = 0 := by
        simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero, mul_zero, zero_div]
        simp
      rw [hzero]
      have hM0 : 0 ≤ max K₁ (K₂ * C₀) := le_trans hK₁pos.le (le_max_left _ _)
      have hS0 : 0 ≤ ∑ i : {i : Fin m // cl i = k}, ‖z i‖ ^ 2 :=
        Finset.sum_nonneg (fun i _ => sq_nonneg _)
      simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, le_refl]
  -- summation over the classes
  have hsplit := pls_integral_class_split (cl := cl) hXpos hUpos hUX a g z hInteg
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hsplit
  have hsumclass : (∑ k : Fin (K + 1), (∫ y in Set.Ioi (0 : ℝ),
        (Real.exp (-(y / X)) - Real.exp (-(y / U)))
        * ‖∑ i : {i : Fin m // cl i = k},
            z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y))
      ≤ max K₁ (K₂ * C₀) * L * X ^ (2 * (1 - σ)) * ∑ i, ‖z i‖ ^ 2 := by
    calc (∑ k : Fin (K + 1), (∫ y in Set.Ioi (0 : ℝ),
          (Real.exp (-(y / X)) - Real.exp (-(y / U)))
          * ‖∑ i : {i : Fin m // cl i = k},
              z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y))
        ≤ ∑ k : Fin (K + 1), max K₁ (K₂ * C₀) * L * X ^ (2 * (1 - σ))
            * ∑ i : {i : Fin m // cl i = k}, ‖z i‖ ^ 2 := Finset.sum_le_sum (fun k _ => hclass k)
      _ = max K₁ (K₂ * C₀) * L * X ^ (2 * (1 - σ))
            * ∑ k : Fin (K + 1), ∑ i : {i : Fin m // cl i = k}, ‖z i‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = max K₁ (K₂ * C₀) * L * X ^ (2 * (1 - σ)) * ∑ i, ‖z i‖ ^ 2 := by
          rw [Fintype.sum_fiberwise cl (fun i => ‖z i‖ ^ 2)]
  -- the final chain
  have hK1le : (K : ℝ) + 1 ≤ 2 * (2 + log2 (1 + (1 - σ) * L)) := by
    have h := Nat.ceil_lt_add_one hlog2nn
    rw [← hKdef] at h
    linarith
  have hXp : X ^ (2 * (1 - σ)) = Dpow q T (2 * p.x * (1 - σ)) := by
    rw [hXdef, Dpow, Dpow]
    rw [← Real.rpow_mul hscale0.le p.x (2 * (1 - σ))]
    congr 1
    ring
  have hM0 : 0 ≤ max K₁ (K₂ * C₀) := le_trans hK₁pos.le (le_max_left _ _)
  have hD0 : 0 ≤ Dpow q T (2 * p.x * (1 - σ)) :=
    Real.rpow_nonneg hscale0.le _
  have hS0 : 0 ≤ ∑ i, ‖z i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc (poleGram m X U ρ z).re
      = ∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
          * ‖∑ i, z i * (y : ℂ) ^ (1 - ρ i)‖ ^ 2 / y := hgram
    _ = ∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U)))
          * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y := hrewrite
    _ ≤ (K + 1 : ℝ) * ∑ k : Fin (K + 1), (∫ y in Set.Ioi (0 : ℝ),
          (Real.exp (-(y / X)) - Real.exp (-(y / U)))
          * ‖∑ i : {i : Fin m // cl i = k},
              z i * (y : ℂ) ^ ((a i : ℂ) - ((g i : ℂ)) * Complex.I)‖ ^ 2 / y) := hsplit
    _ ≤ (K + 1 : ℝ) * (max K₁ (K₂ * C₀) * L * X ^ (2 * (1 - σ)) * ∑ i, ‖z i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsumclass (by positivity)
    _ = ((K : ℝ) + 1) * (max K₁ (K₂ * C₀) * L * X ^ (2 * (1 - σ)) * ∑ i, ‖z i‖ ^ 2) := by
        push_cast; ring
    _ ≤ (2 * (2 + log2 (1 + (1 - σ) * L)))
          * (max K₁ (K₂ * C₀) * L * X ^ (2 * (1 - σ)) * ∑ i, ‖z i‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_right hK1le
        exact mul_nonneg (mul_nonneg (mul_nonneg hM0 hLpos.le)
          (Real.rpow_nonneg hXpos.le _)) hS0
    _ = 2 * max K₁ (K₂ * C₀) * (2 + log2 (1 + (1 - σ) * L)) * L
          * Dpow q T (2 * p.x * (1 - σ)) * ∑ i, ‖z i‖ ^ 2 := by
        rw [hXp]; ring


end Work.ZeroDensity.LogFree
