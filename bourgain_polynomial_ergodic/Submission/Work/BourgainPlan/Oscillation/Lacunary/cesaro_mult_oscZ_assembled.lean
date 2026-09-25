import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_props
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_assembly
import Submission.Work.BourgainPlan.Oscillation.Lacunary.oscZ_cut_weighted
import Submission.Work.BourgainPlan.Oscillation.Lacunary.oscZ_cut_tscale
import Submission.Work.BourgainPlan.Oscillation.Lacunary.dilation_profile_oscZ
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_profile_data

/-!
# The Cesàro (`P = X`) lacunary oscillation inequality, assembled

The four analytic inputs (`WgtCut`, `TScale`, `DilProfile`, `ProfileData`) are supplied by the
sibling modules `oscZ_cut_weighted`, `oscZ_cut_tscale`, `dilation_profile_oscZ` and
`cesaro_profile_data`, and `cesaro_mult_oscZ_of_parts` performs the assembly.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- **The block oscillation of the Cesàro averages along the lacunary scales.**  For `ρ > 1` there
is `C > 0` such that for every strictly increasing chain of scales `k`, every block count `J` and
every finitely supported `f : ℤ → ℂ`, the `ℓ²(ℤ)` block oscillation of the Cesàro averages
`⌊ρ^i⌋⁻¹ Σ_{n<⌊ρ^i⌋} f (· + n)` at the lacunary scales is at most `C² ∫⁻‖f‖²`. -/
theorem cesaro_mult_oscZ_assembled (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
      ∀ (f : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → f n = 0) →
        Work.BourgainPlan.Oscillation.oscZ (fun i x =>
            ∫ θ in (0:ℝ)..1,
              (((Work.BourgainPlan.Oscillation.lacScale ρ i : ℂ))⁻¹ *
                ((Complex.exp (2 * Real.pi * Complex.I *
                    ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)) - 1) /
                 (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) - 1))) *
              (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
              Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
          ≤ ENNReal.ofReal (C^2) *
              ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
  cesaro_mult_oscZ_of_parts ρ hρ (oscZ_cut_weighted ρ hρ)
    (fun C₁ hC₁ h => by
      obtain ⟨C, hC, hbody⟩ := oscZ_cut_tscale ρ hρ C₁ hC₁ h
      exact ⟨C * C₁, by positivity,
        fun t ht r hr cap hcap hbd J k hk f T hf =>
          hbody t ht r hr cap hcap hbd J k hk f T hf⟩)
    (fun C₂ hC₂ h => dilation_profile_oscZ ρ hρ C₂ hC₂ h)
    (cesaro_profile_data ρ hρ)

end

end Work.BourgainPlan.Oscillation.Lacunary
