/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Lipschitz bound `‖matLin X - matLin Y‖ ≤ matSum Δ`

`matLin` is additive in the matrix argument (`matLin_sub`), so the difference of the two
linear maps is `matLin (X - Y)`, whose entries are the differences `X i j - Y i j`.  The row-sum
estimate `norm_matLin_le` then bounds its operator norm by the sum of the absolute values of
those differences, and the hypothesis `|X i j - Y i j| ≤ Δ i j` upgrades each entry to `Δ i j`.
This is the quantitative "difference of two Jacobians" bound used by the Krawczyk criterion.
-/
import Mathlib
import Submission.Work.SeedCertNum.Mat3
import Submission.Work.SeedCertNum.norm_matLin_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

/-- `matLin` is additive in the matrix argument: the linear map of the entrywise difference is
the difference of the two linear maps. -/
theorem matLin_sub (a b : Fin 3 → Fin 3 → ℝ) :
    matLin a - matLin b = matLin (fun i j => a i j - b i j) := by
  apply ContinuousLinearMap.ext
  intro v
  apply eq_of_proj3
  intro i
  simp only [sub_apply, map_sub, matLin_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem norm_matLin_sub_le {X Y Δ : Fin 3 → Fin 3 → ℝ}
    (h : ∀ i j, |X i j - Y i j| ≤ Δ i j) :
    ‖Work.SeedCert.matLin X - Work.SeedCert.matLin Y‖ ≤ Work.SeedCert.matSum Δ := by
  have hsub : matLin X - matLin Y = matLin (fun i j => X i j - Y i j) := matLin_sub X Y
  rw [hsub]
  calc ‖matLin (fun i j => X i j - Y i j)‖
      ≤ matSum (matAbs (fun i j => X i j - Y i j)) := norm_matLin_le _
    _ ≤ matSum Δ := by
        simp only [matSum, matAbs]
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j

end Work.SeedCertNum
