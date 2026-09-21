import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

lemma integral_fin_ball_coord_zero {m : ℕ} [Nonempty (Fin m)] (j : Fin m) (R : ℝ) :
    ∫ y : Fin m → ℝ in {y | ∑ i : Fin m, (y i)^2 ≤ R^2}, y j = 0 := by
  let B : Set (Fin m → ℝ) := {y | ∑ i : Fin m, (y i)^2 ≤ R^2}
  have hB_meas : MeasurableSet B := by
    dsimp [B]
    exact (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hpre : (Neg.neg : (Fin m → ℝ) → (Fin m → ℝ)) ⁻¹' B = B := by
    ext y
    simp [B]
  have hmp : MeasurePreserving (Neg.neg : (Fin m → ℝ) → (Fin m → ℝ)) volume volume :=
    Measure.measurePreserving_neg volume
  have hemb : MeasurableEmbedding (Neg.neg : (Fin m → ℝ) → (Fin m → ℝ)) :=
    measurableEmbedding_neg
  have hchange := hmp.setIntegral_preimage_emb hemb (fun y : Fin m → ℝ => y j) B
  rw [hpre] at hchange
  have hleft : (∫ y in B, (Neg.neg y) j) = ∫ y in B, - (y j) := by
    refine setIntegral_congr_fun hB_meas ?_
    intro y hy
    simp [Pi.neg_apply]
  rw [hleft] at hchange
  have hneg : (∫ y in B, - (y j)) = - (∫ y in B, y j) := by
    simp [integral_neg]
  rw [hneg] at hchange
  -- hchange : - ∫ y in B, y j = ∫ y in B, y j
  have : (∫ y in B, y j) = 0 := by linarith
  simpa [B] using this

end Commons.Geometry.Ulam