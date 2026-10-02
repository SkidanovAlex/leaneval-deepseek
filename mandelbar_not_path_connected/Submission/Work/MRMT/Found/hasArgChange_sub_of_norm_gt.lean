import Mathlib
import Submission.Work.MRMT.QC.plane_surjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

theorem hasArgChange_sub_of_norm_gt {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hloop : γ 1 = γ 0) {M : ℝ} (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖γ t‖ ≤ M) {w : ℂ}
    (hw : M < ‖w‖) :
    Work.MRMT.QC.HasArgChange (fun t => γ t - w) 0 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by norm_num))
  have hwpos : 0 < ‖w‖ := lt_of_le_of_lt hM0 hw
  have hwne : w ≠ 0 := norm_pos_iff.mp hwpos
  set r : ℝ → ℂ := fun t => 1 - γ t / w with hrdef
  have hrcont : ContinuousOn r (Set.Icc 0 1) := by
    rw [hrdef]
    exact continuousOn_const.sub (hγ.div_const w)
  have hrpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (r t).re := by
    intro t ht
    have h1 : ‖γ t / w‖ < 1 := by
      rw [norm_div, div_lt_one hwpos]
      exact lt_of_le_of_lt (hM t ht) hw
    have h2 : (γ t / w).re ≤ ‖γ t / w‖ := Complex.re_le_norm _
    rw [hrdef]
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hrloop : r 1 = r 0 := by
    simp only [hrdef]
    rw [hloop]
  obtain ⟨Θ₀, hA₀, hΔ₀⟩ := Work.MRMT.QC.hasArgChange_const (-w) (neg_ne_zero.mpr hwne)
  have hΔ₀' : Θ₀ 1 - Θ₀ 0 = 0 := by simpa using hΔ₀
  have hA : Work.MRMT.QC.IsArgFunOn (fun t => γ t - w)
      (fun t => Θ₀ t + Real.arcsin ((r t / (‖r t‖ : ℂ)).im)) :=
    (Work.MRMT.QC.isArgFunOn_mul_of_re_pos hA₀ hrcont hrpos).congr (by
      intro t ht
      rw [hrdef]
      field_simp
      ring)
  refine ⟨fun t => Θ₀ t + Real.arcsin ((r t / (‖r t‖ : ℂ)).im), hA, ?_⟩
  have hψ : Real.arcsin ((r 1 / (‖r 1‖ : ℂ)).im) - Real.arcsin ((r 0 / (‖r 0‖ : ℂ)).im) = 0 := by
    rw [hrloop]; ring
  have hcast : ((0 : ℤ) : ℝ) = 0 := by norm_num
  rw [hcast, mul_zero]
  linarith

end Work.MRMT.Found
