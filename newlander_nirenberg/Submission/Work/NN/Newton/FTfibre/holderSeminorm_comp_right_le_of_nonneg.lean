import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.holderNorm_comp_linear
import Submission.Work.NN.Newton.FTfibre.holder_quot_le_nonneg

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Newton.FTfibre

theorem holderSeminorm_comp_right_le_of_nonneg
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : E →L[ℝ] F) (i : ℕ) (m : WithTop ℕ∞) {α : ℝ} (hα : 0 ≤ α) {u : F → ℂ} {s : Set F}
    (hu : ContDiffOn ℝ m u s) (hs : UniqueDiffOn ℝ s) (hs' : UniqueDiffOn ℝ (Φ ⁻¹' s))
    (hin : (i : WithTop ℕ∞) ≤ m) :
    Work.CR.Flat.holderSeminorm i α (fun z => u (Φ z)) (Φ ⁻¹' s)
      ≤ ENNReal.ofReal (‖Φ‖ ^ ((i : ℝ) + α)) * Work.CR.Flat.holderSeminorm i α u s := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  by_cases hxy' : Φ x = Φ y
  · have hDx := Φ.iteratedFDerivWithin_comp_right hu hs hs' hx hin
    have hDy := Φ.iteratedFDerivWithin_comp_right hu hs hs' hy hin
    rw [show (u ∘ ⇑Φ) = (fun z => u (Φ z)) from rfl] at hDx hDy
    have hz : iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) x
        - iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) y = 0 := by
      rw [hDx, hDy, hxy', sub_self]
    rw [hz, norm_zero, zero_div, ENNReal.ofReal_zero]
    exact bot_le
  · have hle : ‖Φ x - Φ y‖ ≤ ‖Φ‖ * ‖x - y‖ := by
      simpa using Φ.le_opNorm (x - y)
    have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hd : 0 < ‖Φ x - Φ y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy')
    have hP : 0 < ‖Φ‖ := by
      by_contra h
      have h0 : ‖Φ‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg Φ)
      rw [h0, zero_mul] at hle
      linarith
    have hNM := Work.NN.Final.norm_iteratedFDerivWithin_comp_right_sub_le
      Φ i m hu hs hs' hin hx hy
    calc ENNReal.ofReal (‖iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) x
            - iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal (‖Φ‖ ^ ((i : ℝ) + α)
            * (‖iteratedFDerivWithin ℝ i u s (Φ x) - iteratedFDerivWithin ℝ i u s (Φ y)‖
              / ‖Φ x - Φ y‖ ^ α)) :=
          ENNReal.ofReal_le_ofReal
            (holder_quot_le_nonneg hα i hNM (norm_nonneg _) hP hr hd hle)
      _ = ENNReal.ofReal (‖Φ‖ ^ ((i : ℝ) + α))
            * ENNReal.ofReal (‖iteratedFDerivWithin ℝ i u s (Φ x)
              - iteratedFDerivWithin ℝ i u s (Φ y)‖ / ‖Φ x - Φ y‖ ^ α) :=
          ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg Φ) _)
      _ ≤ ENNReal.ofReal (‖Φ‖ ^ ((i : ℝ) + α)) * Work.CR.Flat.holderSeminorm i α u s :=
          mul_le_mul_right (Work.CR.Flat.le_holderSeminorm i α u s hx hy hxy') _

end Work.NN.Newton.FTfibre
