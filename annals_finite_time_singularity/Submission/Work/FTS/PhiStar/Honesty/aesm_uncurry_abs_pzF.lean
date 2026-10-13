import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem aesm_uncurry_abs_pzF {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun t θ : ℝ => |Work.Spaces.pz F t θ|))
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- On the open quadrant `(0,∞) × (0,π/2)` the function `(z,θ) ↦ |pz F z θ|` is continuous
  -- (`SmoothOpen.pz`), hence a.e. strongly measurable for the product of the restrictions of
  -- Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]` (`Work.Spaces.aesm_of_continuousOn_Qd`).
  have hbig : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |Work.Spaces.pz F p.1 p.2|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hsm.pz).continuousOn.abs
  -- `Icc a b ⊆ Ioi 0 ⊆ Iz` since `0 < a`, so shrinking the radial measure preserves
  -- a.e. strong measurability.
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := by
    intro t ht
    exact le_trans (le_of_lt ha) ht.1
  have hmono : (MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono hsub le_rfl) le_rfl
  exact hbig.mono_measure hmono

end Work.FTS.PhiStar.Honesty
