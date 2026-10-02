import Mathlib
import Submission.Work.FatouCoord.Main
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_preconnected

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic2

/-- For `z ≠ 0` the two membership conditions of the petal agree: `M < Re (-1/z)` is exactly
`z.re < -M * normSq z`, because `Re (-1/z) = -z.re / normSq z` and `normSq z > 0`. -/
theorem re_neg_one_div_gt_iff {M : ℝ} {z : ℂ} (hz : z ≠ 0) :
    (M < (-1 / z).re ↔ z.re < -M * Complex.normSq z) := by
  have hchart : (-1 / z : ℂ) = Work.FatouCoord.chart z := rfl
  rw [hchart, Work.FatouCoord.re_chart hz, lt_div_iff₀ (Complex.normSq_pos.mpr hz)]
  constructor <;> intro h <;> linarith

/-- For `0 < r` and `1 / r ≤ M` the petal `Petal r M` coincides with the half-plane petal
`HPlanePetal M`: the modulus bound `‖z‖ < r` is automatic from `M < Re (-1/z)` when `M ≥ 1/r`. -/
theorem petal_eq_HPlanePetal {r M : ℝ} (hr : 0 < r) (hMr : 1 / r ≤ M) :
    Work.FatouCoord.Petal r M = Work.FatouCoordFix.HPlanePetal M := by
  have hMpos : 0 < M := lt_of_lt_of_le (one_div_pos.mpr hr) hMr
  ext z
  rw [Work.FatouCoord.mem_Petal, Work.FatouCoordFix.mem_HPlanePetal]
  constructor
  · rintro ⟨hzr, hzre⟩
    have hz0 : z ≠ 0 := by rintro rfl; simp at hzre
    exact ⟨hz0, (re_neg_one_div_gt_iff hz0).mpr hzre⟩
  · rintro ⟨hz0, hzre⟩
    have hlt : z.re < -M * Complex.normSq z := (re_neg_one_div_gt_iff hz0).mp hzre
    refine ⟨?_, hlt⟩
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have h4 : M * Complex.normSq z < -z.re := by linarith
    have h5 : -z.re ≤ ‖z‖ := by
      have := Complex.abs_re_le_norm z
      rw [abs_le] at this
      linarith [this.1]
    have h7 : M * ‖z‖ < 1 := by
      rw [Complex.normSq_eq_norm_sq] at h4
      nlinarith
    have h6 : ‖z‖ < 1 / M := by
      rw [lt_div_iff₀ hMpos]
      linarith
    have hinv : 1 / M ≤ r := by
      rw [div_le_iff₀ hMpos]
      have h1 : (1 : ℝ) ≤ M * r := by
        rw [← div_le_iff₀ hr]
        exact hMr
      linarith
    linarith

/-- **The Leau--Fatou petal `Petal r M` is preconnected.**  For `0 < r` and `1 / r ≤ M` the petal
`Work.FatouCoord.Petal r M = {z | ‖z‖ < r ∧ z.re < -M * normSq z}` is the image of the half-plane
`{w | M < w.re}` under the parabolic chart `w ↦ -1 / w`: for such `M` the two membership conditions
`‖z‖ < r` and `M < (-1/z).re` are equivalent, and images of preconnected sets under continuous
maps are preconnected.

Route: `Work.FatouCoordFix.HPetal.HPlanePetal_preconnected` (`0 ≤ M`), after identifying
`Work.FatouCoord.Petal r M = Work.FatouCoordFix.HPlanePetal M` for `0 < r`, `M ≥ 1/r`
(`HPlanePetal M = {u | u ≠ 0 ∧ M < (-1/u).re}` and `Petal r M ⊆ ball 0 r` is then automatic). -/
theorem isPreconnected_petal {r M : ℝ} (hr : 0 < r) (hMr : 1 / r ≤ M) :
    IsPreconnected (Work.FatouCoord.Petal r M) := by
  have hMpos : 0 < M := lt_of_lt_of_le (one_div_pos.mpr hr) hMr
  rw [petal_eq_HPlanePetal hr hMr]
  exact Work.FatouCoordFix.HPetal.HPlanePetal_preconnected (le_of_lt hMpos)

end Work.FatouParabolic2
