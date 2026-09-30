import Mathlib
import Submission.Work.RTInstance.Models

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTInstance

/-- **The height factor of the total UHS model is strictly positive.**  Writing
`t = smoothTransition (s / δ)`, `uhsFactor δ s = t·s⁻¹ + (1-t)·δ⁻¹`: for `s ≤ 0` this is `δ⁻¹`,
for `δ ≤ s` it is `s⁻¹`, and for `0 < s < δ` we have `uhsFactor δ s = t·(s⁻¹ - δ⁻¹) + δ⁻¹` with
`s⁻¹ > δ⁻¹` and `t ≥ 0`. -/
theorem uhsFactor_pos {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : 0 < uhsFactor δ s := by
  rw [uhsFactor]
  have hδinv : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hnc : 0 ≤ Real.smoothTransition (s / δ) := Real.smoothTransition.nonneg _
  rcases le_or_gt s 0 with hs | hs
  · have hz : Real.smoothTransition (s / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs hδ.le)
    rw [hz]; simpa using hδinv
  · rcases le_or_gt δ s with hds | hsd
    · have ho : Real.smoothTransition (s / δ) = 1 :=
        Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hδ]; linarith)
      rw [ho]
      have hsinv : 0 < s⁻¹ := inv_pos.mpr hs
      simpa using hsinv
    · have hlt : δ⁻¹ < s⁻¹ := (inv_lt_inv₀ hδ hs).mpr hsd
      have key : 0 < s⁻¹ - δ⁻¹ := by linarith
      have hthis : 0 < Real.smoothTransition (s / δ) * (s⁻¹ - δ⁻¹) + δ⁻¹ := by
        nlinarith [hnc, key, hδinv]
      have heq : Real.smoothTransition (s / δ) * s⁻¹ + (1 - Real.smoothTransition (s / δ)) * δ⁻¹
          = Real.smoothTransition (s / δ) * (s⁻¹ - δ⁻¹) + δ⁻¹ := by ring
      rw [heq]; exact hthis

/-- **The total UHS model is positive definite.**  `uhsModel δ q v v = uhsFactor δ (q 3)² · ⟪v,v⟫`
is a product of two strictly positive factors: the squared height factor, positive by
`uhsFactor_pos`, and the squared norm `⟪v,v⟫ > 0` because `v ≠ 0`. -/
theorem uhsModel_pos (δ : ℝ) (hδ : 0 < δ) (q : E4) (v : E4) (hv : v ≠ 0) :
    0 < uhsModel δ q v v := by
  rw [uhsModel_apply]
  exact mul_pos (pow_pos (uhsFactor_pos hδ (q 3)) 2) (real_inner_self_pos.mpr hv)

end Work.RTInstance
