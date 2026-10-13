import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeColl

theorem sliceWBound (η K : ℝ) (hη : 0 < η) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ) (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi / 2) (f : ℝ → ℝ),
      ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv f θ)^2 * (Real.sin (2*θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (f θ)^2 ≤ K * θ ^ (1 + η)
        * (∫ t in Set.Ioo 0 θ, (deriv f t)^2 * (Real.sin (2*t)) ^ (-η))) →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (f θ)^2 ≤ K * (Real.pi/2 - θ) ^ (1 + η)
        * (∫ t in Set.Ioo θ (Real.pi/2), (deriv f t)^2 * (Real.sin (2*t)) ^ (-η))) →
      |∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin (2*θ)) ^ (-η)
          * deriv (deriv (fun θ' => Real.smoothTransition ((θ' - δ/4)/(δ/4))
              * Real.smoothTransition (((Real.pi/2 - δ/4) - θ')/(δ/4)))) θ * (f θ)^2|
        ≤ C * K * ((∫ θ in Set.Ioo 0 δ, (Real.sin (2*θ)) ^ (-η) * (deriv f θ)^2)
            + (∫ θ in Set.Ioo (Real.pi/2 - δ) (Real.pi/2),
                (Real.sin (2*θ)) ^ (-η) * (deriv f θ)^2)) := by sorry

end Work.FTS.EllipticEst.AeColl
