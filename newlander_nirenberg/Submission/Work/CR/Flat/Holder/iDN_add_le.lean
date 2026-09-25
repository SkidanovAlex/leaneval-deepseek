import Mathlib
import Submission.Work.CR.Flat.Holder.Bilinear

namespace Work.CR.Flat.Holder

theorem iDN_add_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (i : ℕ) {φ ψ : X → A} {Ω : Set X}
    (hφ : ContDiffOn ℝ (i : ℕ∞) φ Ω) (hψ : ContDiffOn ℝ (i : ℕ∞) ψ Ω)
    (hΩ : UniqueDiffOn ℝ Ω) :
    iDN i (φ + ψ) Ω ≤ iDN i φ Ω + iDN i ψ Ω := by
  refine iSup₂_le fun x hx => ?_
  rw [iteratedFDerivWithin_add_apply (hφ.contDiffWithinAt hx) (hψ.contDiffWithinAt hx) hΩ hx]
  calc ENNReal.ofReal
        ‖iteratedFDerivWithin ℝ i φ Ω x + iteratedFDerivWithin ℝ i ψ Ω x‖
      ≤ ENNReal.ofReal (‖iteratedFDerivWithin ℝ i φ Ω x‖ + ‖iteratedFDerivWithin ℝ i ψ Ω x‖) :=
        ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖iteratedFDerivWithin ℝ i φ Ω x‖ + ENNReal.ofReal ‖iteratedFDerivWithin ℝ i ψ Ω x‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ iDN i φ Ω + iDN i ψ Ω := add_le_add (le_iDN i hx) (le_iDN i hx)

end Work.CR.Flat.Holder
