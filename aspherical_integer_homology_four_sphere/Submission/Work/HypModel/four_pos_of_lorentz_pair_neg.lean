import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Time orientation of timelike vectors in `ℝ^{1,4}`

Two unit timelike vectors `u`, `v` (i.e. `⟨u,u⟩ = ⟨v,v⟩ = -1`, points of the hyperboloid) whose
pairing is negative lie in the same time orientation: if `v` points to the future (`v 4 > 0`) and
`⟨u,v⟩ < 0`, then `u` also points to the future (`u 4 > 0`).

The proof is the standard reversed Cauchy–Schwarz argument, done in coordinates: writing
`a = proj4 u`, `b = proj4 v` for the spatial parts, the hypothesis `⟨u,u⟩ = -1` gives
`‖a‖² = (u 4)² - 1 ≤ (u 4)²`, hence `‖a‖ ≤ |u 4|`, and likewise `‖b‖ ≤ |v 4|`.  Cauchy–Schwarz in
`ℝ⁴` then bounds `⟨u,v⟩ = ⟪a,b⟫ - u 4 v 4 ≥ -‖a‖‖b‖ - u 4 v 4 ≥ -|u 4| v 4 - u 4 v 4`, which is
`≥ 0` on the future sheet -- so a negative pairing forces `u 4 > 0`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace

theorem four_pos_of_lorentz_pair_neg {u v : V5} (hu : lorentz u u = -1)
    (hv : lorentz v v = -1) (hv4 : 0 < v 4) (huv : lorentz u v < 0) : 0 < u 4 := by
  by_contra h
  rw [not_lt] at h
  -- spatial norms: ‖proj4 u‖² = (u 4)² - 1, ‖proj4 v‖² = (v 4)² - 1
  have hua : ‖proj4 u‖ ^ 2 = (u 4) ^ 2 - 1 := by
    have h1 := hu
    rw [lorentz_eq_dotProduct_proj4, ← inner_eq_dotProduct, real_inner_self_eq_norm_sq] at h1
    linarith
  have hvb : ‖proj4 v‖ ^ 2 = (v 4) ^ 2 - 1 := by
    have h1 := hv
    rw [lorentz_eq_dotProduct_proj4, ← inner_eq_dotProduct, real_inner_self_eq_norm_sq] at h1
    linarith
  -- hence the spatial norms are bounded by the time coordinates
  have hA : ‖proj4 u‖ ≤ -u 4 := by
    have h2 : ‖proj4 u‖ ^ 2 ≤ (u 4) ^ 2 := by nlinarith [hua]
    have h3 : |‖proj4 u‖| ≤ |u 4| := sq_le_sq.mp h2
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonpos h] at h3
    exact h3
  have hB : ‖proj4 v‖ ≤ v 4 := by
    have h2 : ‖proj4 v‖ ^ 2 ≤ (v 4) ^ 2 := by nlinarith [hvb]
    have h3 : |‖proj4 v‖| ≤ |v 4| := sq_le_sq.mp h2
    rw [abs_of_nonneg (norm_nonneg _), abs_of_pos hv4] at h3
    exact h3
  have hmul : ‖proj4 u‖ * ‖proj4 v‖ ≤ (-u 4) * v 4 :=
    mul_le_mul hA hB (norm_nonneg _) (by linarith)
  -- Cauchy–Schwarz in ℝ⁴
  have hcs : -(‖proj4 u‖ * ‖proj4 v‖) ≤ ⟪proj4 u, proj4 v⟫_ℝ := by
    have h3 := abs_real_inner_le_norm (proj4 u) (proj4 v)
    rw [abs_le] at h3
    exact h3.1
  -- put the pieces together: the pairing is nonnegative, contradicting `huv`
  have hle : 0 ≤ lorentz u v := by
    rw [lorentz_eq_dotProduct_proj4, ← inner_eq_dotProduct]
    nlinarith [hcs, hmul]
  linarith [hle, huv]

end Work.HypModel
