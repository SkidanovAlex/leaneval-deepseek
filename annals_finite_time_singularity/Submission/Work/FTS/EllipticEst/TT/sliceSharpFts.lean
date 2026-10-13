import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngAWeak.sliceIbpSigmaWeakFts
import Submission.Work.FTS.EllipticEst.AngAWeak.cosSqHardyWeakFts
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

theorem sliceSharpFts {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∃ M : ℝ, 0 ≤ M ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + (2 * Work.Spaces.eta) * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  -- The two ingredients are the weak-class integration by parts for the angular slice
  -- (`sliceIbpSigmaWeakFts`) and the sharp `cos²(2θ)`-weighted Hardy inequality
  -- (`cosSqHardyWeakFts`), both with the weight `σ = sin(2θ)^{-η}`, `η = 99/100`:
  --   `∫ (f')²σ = -∫ f f''σ + 2η∫ f²σ + 2η(1+η)∫ f²cos²(2θ)σ/sin²(2θ)`,
  --   `∫ f²cos²(2θ)σ/sin²(2θ) ≤ (1+η)^{-2} ∫ (f')²σ`.
  -- Combining them: `∫ f f''σ ≤ -(1 - 2η/(1+η))∫(f')²σ + 2η∫f²σ` and
  -- `1 - 2η/(1+η) = (1-η)/(1+η)`, which is the claim.
  obtain ⟨M, hM0, hMf, hMd⟩ := hb
  have hη0 : (0 : ℝ) ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have hhardy := Work.FTS.EllipticEst.AngAWeak.cosSqHardyWeakFts Work.Spaces.eta hη0 hη1 f hf
    ⟨M, hM0, hMf, hMd⟩
  have hibp := Work.FTS.EllipticEst.AngAWeak.sliceIbpSigmaWeakFts Work.Spaces.eta hη0 hη1 f M hM0
    hf hMf hMd h2
  set D : ℝ := ∫ θ in Work.Spaces.Iθ,
    (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hD
  set G : ℝ := ∫ θ in Work.Spaces.Iθ,
    f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hG
  set H : ℝ := ∫ θ in Work.Spaces.Iθ,
    (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hH
  set E : ℝ := ∫ θ in Work.Spaces.Iθ,
    (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) with hE
  have hid : D = -G + 2 * Work.Spaces.eta * H + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * E :=
    hibp
  have hc0 : (0 : ℝ) ≤ 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) := by
    norm_num [Work.Spaces.eta]
  -- the sharp Hardy inequality with the coefficient `2η(1+η)`
  have hEbound : 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * E
      ≤ (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * D := by
    have h1 : 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * E
        ≤ 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (1 / (1 + Work.Spaces.eta) ^ 2 * D) :=
      mul_le_mul_of_nonneg_left hhardy hc0
    have h2 : 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
          * (1 / (1 + Work.Spaces.eta) ^ 2 * D)
        = (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * D := by
      rw [show 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
            * (1 / (1 + Work.Spaces.eta) ^ 2 * D)
          = (2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
              * (1 / (1 + Work.Spaces.eta) ^ 2)) * D from by ring]
      rw [show 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
            * (1 / (1 + Work.Spaces.eta) ^ 2)
          = 2 * Work.Spaces.eta / (1 + Work.Spaces.eta) from by
        norm_num [Work.Spaces.eta]]
    exact le_trans h1 (le_of_eq h2)
  have hkey : -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
      = -1 + 2 * Work.Spaces.eta / (1 + Work.Spaces.eta) := by
    norm_num [Work.Spaces.eta]
  have hGle : G ≤ (-1 + 2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * D
      + 2 * Work.Spaces.eta * H := by
    linarith [hid, hEbound]
  rw [hkey]
  simpa only [hG, hD, hH] using hGle

end Work.FTS.EllipticEst.TT
