import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.Construction.Defs
import Submission.Work.FM.Core
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge.Pieces

theorem L12_split_of_slice_integrable {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (ha : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (hb : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (hSum : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (fun z θ => a z θ + b z θ)) (Set.Ioi 0))
    (hA : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K a) (Set.Ioi 0)) :
    ∀ z : ℝ, 0 ≤ z →
      Work.Construction.L12 (fun z θ => a z θ + b z θ) z
        = Work.Construction.L12 a z + Work.Construction.L12 b z := by
  intro z hz
  -- Restrict the two radial integrability hypotheses to `(z,∞)`: `z ≥ 0` gives `(z,∞) ⊆ (0,∞)`.
  have hA' : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K a) (Set.Ioi z) :=
    hA.mono_set (Set.Ioi_subset_Ioi hz)
  -- The density of `b` is the difference of the densities of `a + b` and of `a` on `(z,∞)`:
  -- both of these are integrable there, so `L12dens K b` is too.
  have hB' : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K b) (Set.Ioi z) := by
    refine ((hSum.sub hA).mono_set (Set.Ioi_subset_Ioi hz)).congr_fun ?_ measurableSet_Ioi
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hz hs
    have hadd := Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
      (ha s hs0) (hb s hs0)
    simp only [Pi.sub_apply]
    linarith
  -- The densities add pointwise on `(z,∞)`, and the two halves are integrable there.
  simp only [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s hs => Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
      (ha s (lt_of_le_of_lt hz hs)) (hb s (lt_of_le_of_lt hz hs)))]
  exact MeasureTheory.integral_add hA' hB'

end Work.FTS.MeridianDyn.Bridge.Pieces
