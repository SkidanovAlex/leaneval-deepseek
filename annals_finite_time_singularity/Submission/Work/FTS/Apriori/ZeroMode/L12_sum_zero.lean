import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Additivity of the `L₁₂` zero mode over finite sums

The operator `L₁₂^K(f)(ρ) = ∫_ρ^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds` is the composition of the
angular integral and the radial integral, both of which are additive over finite sums as soon as
the summands are integrable (`MeasureTheory.integral_finsetSum`).  The two families of
integrability hypotheses in the statement are precisely what is needed: the angular slices on
`Iθ` for `z > 0` (the only `z` for which the density is used, as `L₁₂(·)(0)` integrates over
`Ioi 0`) and the radial integrability of each density on `Ioi 0`.

Since the angular identity only holds for `z > 0`, the density of the sum is compared with the
sum of the densities *on* `Ioi 0` and transported to the radial integral by
`MeasureTheory.setIntegral_congr_fun` (a congruent integral needs no integrability).
-/

namespace Work.FTS.Apriori.ZeroMode

open MeasureTheory Set

theorem L12_sum_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℝ → ℝ → ℝ)
    (hθ : ∀ i ∈ s, ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * F i z θ / z) Work.Spaces.Iθ)
    (hF : ∀ i ∈ s, MeasureTheory.IntegrableOn
      (fun z => Work.Construction.L12dens (F i) z) (Set.Ioi 0)) :
    Work.Construction.L12 (fun z θ => ∑ i ∈ s, F i z θ) 0
      = ∑ i ∈ s, Work.Construction.L12 (F i) 0 := by
  -- Unfold the two layer of definitions on the densities on the right-hand side.
  have hF' : ∀ i ∈ s, MeasureTheory.IntegrableOn
      (fun z => Work.FM.L12dens Work.Spaces.K (F i) z) (Set.Ioi 0) := by
    intro i hi
    simpa only [Work.Construction.L12dens] using hF i hi
  -- The angular density of the sum is the sum of the angular densities, for `z > 0`.
  have hdens : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.FM.L12dens Work.Spaces.K (fun z θ => ∑ i ∈ s, F i z θ) z
        = ∑ i ∈ s, Work.FM.L12dens Work.Spaces.K (F i) z := by
    intro z hz
    have hzpos : 0 < z := hz
    have hcongr : (∫ θ in Set.Icc 0 (Real.pi / 2),
          Work.Spaces.K θ * (∑ i ∈ s, F i z θ) / z)
        = ∫ θ in Set.Icc 0 (Real.pi / 2),
            ∑ i ∈ s, Work.Spaces.K θ * F i z θ / z := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [Finset.mul_sum, Finset.sum_div]
    simp only [Work.FM.L12dens]
    rw [hcongr]
    exact MeasureTheory.integral_finsetSum s (fun i hi => hθ i hi z hzpos)
  -- The radial integral, written through the (unfolded) definition of `L₁₂`.
  have houter :
      (∫ z in Set.Ioi (0 : ℝ),
          Work.FM.L12dens Work.Spaces.K (fun z θ => ∑ i ∈ s, F i z θ) z)
        = ∑ i ∈ s, ∫ z in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K (F i) z := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hdens]
    exact MeasureTheory.integral_finsetSum s hF'
  simpa only [Work.Construction.L12, Work.FM.L12] using houter

end Work.FTS.Apriori.ZeroMode
