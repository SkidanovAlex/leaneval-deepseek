import Mathlib
import Submission.Work.Drive.Mono.CutTransverse

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
/-- A point whose box norm equals `s` is at distance at most `R` from the centre, with `R` proportional to `|s|`. -/
theorem exists_bound_boxNorm_eq (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y : R3, Submission.boxNorm c σ y = s → ‖y - c‖ ≤ R := by
  -- The box norm is a maximum of the three `σ`-permuted scaled coordinate deviations, so
  -- `boxNorm c σ y = s` bounds every coordinate deviation by `2s` (all `boxSide` are `≤ 2`),
  -- hence `‖y - c‖² ≤ 12 s²`.
  refine ⟨Real.sqrt (12 * s ^ 2), Real.sqrt_nonneg _, ?_⟩
  intro y hy
  have hs : 0 ≤ s := by rw [← hy]; exact Submission.boxNorm_nonneg c σ y
  have hterm : ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ 2 * s := by
    intro i
    have hle : |y (σ i) - c (σ i)| / Submission.boxSide i ≤ s := by
      rw [← hy, Submission.boxNorm]
      fin_cases i
      · exact le_trans (le_max_left _ _) (le_max_left _ _)
      · exact le_trans (le_max_right _ _) (le_max_left _ _)
      · exact le_max_right _ _
    rw [div_le_iff₀ (Submission.boxSide_pos i)] at hle
    nlinarith [Submission.boxSide_le_two i, hs, hle]
  have hcoord : ∀ i : Fin 3, ‖(y - c) i‖ ≤ 2 * s := by
    intro i
    have h := hterm (σ.symm i)
    simpa using h
  have hsum : ∑ i : Fin 3, ‖(y - c) i‖ ^ 2 ≤ 12 * s ^ 2 := by
    calc ∑ i : Fin 3, ‖(y - c) i‖ ^ 2
        ≤ ∑ _i : Fin 3, (2 * s) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          nlinarith [hcoord i, norm_nonneg ((y - c) i), hs]
      _ = 12 * s ^ 2 := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
          ring
  have hnormsq : ‖y - c‖ ^ 2 = ∑ i : Fin 3, ‖(y - c) i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  have hle2 : ‖y - c‖ ^ 2 ≤ (Real.sqrt (12 * s ^ 2)) ^ 2 := by
    rw [hnormsq, Real.sq_sqrt (by positivity)]
    exact hsum
  nlinarith [hle2, norm_nonneg (y - c), Real.sqrt_nonneg (12 * s ^ 2)]

end Work.Drive.Mono
