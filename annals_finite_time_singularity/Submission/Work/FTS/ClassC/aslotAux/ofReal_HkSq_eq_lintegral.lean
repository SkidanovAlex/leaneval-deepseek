import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.aslotAux

/-- Under the honesty hypothesis `HkMem`, the `lintegral` of the `ofReal`-integrand of `HkSq` is
the `ofReal` of the real iterated integral `HkSq α k f`. -/
theorem ofReal_HkSq_eq_lintegral {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α k f) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      = ENNReal.ofReal (Work.Spaces.HkSq α k f) := by
  -- The angular slice `z ↦ ∫_θ HkIntegrand α k f z θ` is nonnegative.
  have hnn1 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz]
      fun s => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f s σ :=
    Eventually.of_forall fun s =>
      integral_nonneg fun σ => Work.Spaces.HkIntegrand_nonneg α k f s σ
  -- The outer Bochner integral of the nonnegative integrand is the `ofReal`-integral of its
  -- `lintegral`, by `HkMem.2`.
  have hstep : ENNReal.ofReal (Work.Spaces.HkSq α k f)
      = ∫⁻ s in Work.Spaces.Iz,
          ENNReal.ofReal (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f s σ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal h.2 hnn1
  rw [hstep]
  -- On `Iz` the same collapse holds slicewise, by `HkMem.1`.
  refine MeasureTheory.lintegral_congr_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici ?_)
  intro s hs
  have hnn2 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      fun σ => Work.Spaces.HkIntegrand α k f s σ :=
    Eventually.of_forall fun σ => Work.Spaces.HkIntegrand_nonneg α k f s σ
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (h.1 s hs) hnn2).symm

end Work.FTS.ClassC.aslotAux
