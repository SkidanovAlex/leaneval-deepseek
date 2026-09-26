import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.SummableMulExpNeg

set_option linter.unusedVariables false

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- The norm of `exp (-(2 π y m))` is `t ^ m` with `t = exp (-(2 π y))`. -/
private lemma gen_norm_exp_neg_eq (y : ℝ) (m : ℕ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m : ℝ)))‖
      = Real.exp (-(2 * Real.pi * y)) ^ m := by
  rw [Complex.norm_exp]
  have hre : (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m : ℝ))).re
      = (m : ℝ) * (-(2 * Real.pi * y)) := by
    push_cast
    simp
    ring
  rw [hre, Real.exp_nat_mul]

/-- A polynomial weight times a geometric sequence with ratio `t ∈ [0,1)` is summable. -/
private lemma gen_summable_nat_add_one_pow_mul_geometric {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ N * t ^ n := by
  have htabs : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
  have hgeom : Summable fun n : ℕ => (n : ℝ) ^ N * t ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one N htabs
  have hgeom1 : Summable fun n : ℕ => t ^ n := summable_geometric_of_norm_lt_one htabs
  have hmain : Summable fun n : ℕ => (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) :=
    (hgeom.add hgeom1).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmain
  have hb : ((n : ℝ) + 1) ^ N ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) := by
    have hmax : ((n : ℝ) + 1) ≤ 2 * max (n : ℝ) 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]; linarith
      · rw [max_eq_right hh.le]; linarith
    have hstep : ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N :=
      pow_le_pow_left₀ (by positivity) hmax N
    have hmaxN : (max (n : ℝ) 1) ^ N ≤ (n : ℝ) ^ N + 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]
        have : (0 : ℝ) ≤ (n : ℝ) ^ N := by positivity
        linarith
      · rw [max_eq_right hh.le]; simp
    calc ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N := hstep
      _ = (2 : ℝ) ^ N * (max (n : ℝ) 1) ^ N := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) :=
          mul_le_mul_of_nonneg_left hmaxN (by positivity)
  calc ((n : ℝ) + 1) ^ N * t ^ n ≤ ((2 : ℝ) ^ N * ((n : ℝ) ^ N + 1)) * t ^ n :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) := by ring

/-- **Exponential decay beats polynomial growth.**  A sequence on `Set.Ici k₀` whose
norm grows at most polynomially of degree `N` is still summable after multiplication
by the exponentially decaying factor `exp (-(2 π y m))`, `y > 0`. -/
theorem GenSummableMulExpNeg {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {N : ℕ} {C y : ℝ} (hC : 0 ≤ C)
    (hy : 0 < y) (h : ∀ m, ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    Summable fun m : Set.Ici k₀ =>
      c m * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ))) := by
  set t : ℝ := Real.exp (-(2 * Real.pi * y)) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := by
    rw [ht, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos, hy]
  have hnorm : ∀ m : Set.Ici k₀,
      ‖Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ)))‖ = t ^ (m.1) := by
    intro m
    rw [ht, gen_norm_exp_neg_eq]
  have hw : Summable fun m : Set.Ici k₀ => ((m.1 : ℝ) + 1) ^ N * t ^ (m.1) :=
    (gen_summable_nat_add_one_pow_mul_geometric ht0.le ht1).subtype _
  refine Summable.of_norm_bounded (hw.mul_left C) (fun m => ?_)
  rw [norm_mul, hnorm]
  calc ‖c m‖ * t ^ (m.1) ≤ (C * ((m.1 : ℝ) + 1) ^ N) * t ^ (m.1) :=
        mul_le_mul_of_nonneg_right (h m) (pow_nonneg ht0.le _)
    _ = C * (((m.1 : ℝ) + 1) ^ N * t ^ (m.1)) := by ring

end Work.FunctionalEquations
