/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The operator-norm bound `‖matLin a‖ ≤ matSum (matAbs a)`

`E3 = ℝ × (ℝ × ℝ)` carries the sup norm, so every coordinate functional `proj3 j` is
`1`-Lipschitz (`norm_proj3_le`) and the sup norm is dominated by the sum of the three
coordinate norms (`norm_le_sum_proj3`).  Since `matLin a` is the matrix of `a` and
`proj3 i (matLin a v) = ∑ j a i j * proj3 j v = (matLin_apply)`, the `i`-th row of
`matLin a v` is bounded by `(∑ j |a i j|) * ‖v‖` (`norm_proj3_matLin_le`); summing the three
rows gives the stated bound, which is the crude row-sum estimate used by the Krawczyk
criterion of item A1 to dominate the linear part of the Newton operator.
-/
import Mathlib
import Submission.Work.SeedCertNum.Mat3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

/-- Each coordinate functional on `E3` is `1`-Lipschitz for the sup norm. -/
theorem norm_proj3_le (v : E3) (i : Fin 3) : ‖proj3 i v‖ ≤ ‖v‖ := by
  fin_cases i
  · simpa [proj3_apply] using norm_fst_le v
  · exact le_trans (norm_fst_le v.2) (norm_snd_le v)
  · exact le_trans (norm_snd_le v.2) (norm_snd_le v)

/-- The sup norm on `E3` is bounded by the sum of the three coordinate norms. -/
theorem norm_le_sum_proj3 (w : E3) : ‖w‖ ≤ ‖proj3 0 w‖ + ‖proj3 1 w‖ + ‖proj3 2 w‖ := by
  have h0 : proj3 0 w = w.1 := by simp [proj3_apply]
  have h1 : proj3 1 w = w.2.1 := by simp [proj3_apply]
  have h2 : proj3 2 w = w.2.2 := by simp [proj3_apply]
  have hw1 : (0 : ℝ) ≤ ‖w.1‖ := norm_nonneg _
  have hw2 : (0 : ℝ) ≤ ‖w.2.1‖ := norm_nonneg _
  have hw3 : (0 : ℝ) ≤ ‖w.2.2‖ := norm_nonneg _
  rw [h0, h1, h2, Prod.norm_def, Prod.norm_def]
  apply max_le
  · linarith
  · apply max_le <;> linarith

/-- Row-by-row bound for `matLin a`: `‖(matLin a v)_i‖ ≤ (∑ j |a i j|) * ‖v‖`. -/
theorem norm_proj3_matLin_le (a : Fin 3 → Fin 3 → ℝ) (v : E3) (i : Fin 3) :
    ‖proj3 i (matLin a v)‖ ≤ (∑ j, |a i j|) * ‖v‖ := by
  rw [matLin_apply]
  calc ‖∑ j : Fin 3, a i j * proj3 j v‖
      ≤ ∑ j : Fin 3, ‖a i j * proj3 j v‖ := norm_sum_le _ _
    _ = ∑ j : Fin 3, |a i j| * ‖proj3 j v‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin 3, |a i j| * ‖v‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (norm_proj3_le v j) (abs_nonneg _)
    _ = (∑ j : Fin 3, |a i j|) * ‖v‖ := by rw [Finset.sum_mul]

/-- The operator norm of `matLin a` is at most the sum of the absolute values of the entries
of `a`. -/
theorem norm_matLin_le (a : Fin 3 → Fin 3 → ℝ) :
    ‖Work.SeedCert.matLin a‖ ≤ Work.SeedCert.matSum (Work.SeedCert.matAbs a) := by
  have hM : 0 ≤ matSum (matAbs a) := by
    simp only [matSum, matAbs]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun v => ?_
  calc ‖matLin a v‖
      ≤ ‖proj3 0 (matLin a v)‖ + ‖proj3 1 (matLin a v)‖ + ‖proj3 2 (matLin a v)‖ :=
        norm_le_sum_proj3 _
    _ ≤ (∑ j, |a 0 j|) * ‖v‖ + (∑ j, |a 1 j|) * ‖v‖ + (∑ j, |a 2 j|) * ‖v‖ := by
        linarith [norm_proj3_matLin_le a v 0, norm_proj3_matLin_le a v 1,
          norm_proj3_matLin_le a v 2]
    _ = (∑ i : Fin 3, ∑ j : Fin 3, |a i j|) * ‖v‖ := by
        rw [Fin.sum_univ_three (fun i => ∑ j : Fin 3, |a i j|)]
        ring
    _ = matSum (matAbs a) * ‖v‖ := rfl

end Work.SeedCertNum
