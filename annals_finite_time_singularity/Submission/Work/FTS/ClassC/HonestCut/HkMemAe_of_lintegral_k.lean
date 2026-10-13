import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.HonestCut.HkMemAe_of_lintegral
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.HonestCut

theorem HkMemAe_of_lintegral_k {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hslmeas : ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hfin : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ)) ≤ ENNReal.ofReal C)
    (hmeas : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        (Set.Ioi 0) := by
  -- The `H^k` integrand is a sum of squares (`Work.Spaces.HkIntegrand_nonneg`), so the
  -- general measure-theory principle of `HkMemAe_of_lintegral` applies verbatim; the only
  -- difference from the level-`0` statement is the shape of the integrand, which is
  -- nonnegative for every `k`.
  exact ae_integrableOn_and_integrableOn_of_lintegral_le
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    (fun z hz => hslmeas z (Set.Ioi_subset_Ici_self hz)) hfin hmeas

end Work.FTS.ClassC.HonestCut
