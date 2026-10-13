import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.T1HardSlice
import Submission.Work.H2.T1Q.HardBoundQ
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.H2.T3Q

/-- The angular ("hard", order-five) part of Elgindi's `Transport3` for the `D_θ`-pairing in the
interior class `SmoothQuad`: for `f, g` genuinely `C^∞` on the open quadrant, `g ∈ ℋ⁴`, and
pointwise bounds `|f| ≤ Kf`, `|D_θf| ≤ Kf` on `(0,π/2)`, the `z`-integral of the absolute angular
integral of `T1Hard` is bounded by `C Kf |g|²_{ℋ⁴}`.
The proof is a verbatim copy of `Work.H2.T1Q.HardBoundQ` (same `slice_bound` +
`Cutoff`/`IbpCutoff`/`SliceLimit`/`ShrinkInt`/`SlotBoundQ` argument), whose body never uses the
`DecayAll 4 f`, `HkMem α 4 f` (nor `DecayAll 4 g`) hypotheses of that sibling. -/
theorem HardTheta : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf : ℝ),
    0 < α → α ≤ 1 → Work.FTS.LocData.SmoothQuad f → Work.FTS.LocData.SmoothQuad g →
    Work.Spaces.HkMem α 4 g →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Kf) →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dth f z θ| ≤ Kf) →
    0 ≤ Kf →
    MeasureTheory.IntegrableOn
        (fun z => |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ|) Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ|
        ≤ C * Kf * Work.Spaces.HkSq α 4 g := by
  refine ⟨3 / 2, by norm_num, ?_⟩
  intro α f g Kf hα hα1 hsmf hsmg hmg hKf hKfd hKf0
  -- The per-slice bound: `Work.H2.T1Q.slice_bound` takes *exactly* the hypotheses we have.
  have hslice := Work.H2.T1Q.slice_bound α Kf f g hα hα1 hKf0 hsmf hsmg hmg hKf hKfd
  -- Joint almost-everywhere strong measurability, from continuity on the open quadrant.
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.H2.T1Q.T1HardAesmQ α f g hsmf hsmg).integral_prod_right'
    simpa only using h
  have hdomI : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmg.2
  have hdom : MeasureTheory.Integrable
      (fun z => (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hdomI.const_mul _
  constructor
  · have h : MeasureTheory.Integrable
        (fun z => ‖∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ‖)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.mono' hdom haesm.norm
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => by
          simpa [Real.norm_eq_abs] using hslice z hz))
    simpa only [MeasureTheory.IntegrableOn, Real.norm_eq_abs] using h
  · have hmono := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => abs_nonneg _)) hdom
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hslice z hz))
    calc ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ|
        ≤ ∫ z in Work.Spaces.Iz,
            (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := hmono
      _ = (3 / 2) * Kf * Work.Spaces.HkSq α 4 g := by
          rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]

end Work.FTS.H2.T3Q
