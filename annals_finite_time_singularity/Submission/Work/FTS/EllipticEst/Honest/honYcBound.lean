import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.honestBarLim
import Submission.Work.FTS.EllipticEst.Honest.sliceBarSq2
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.EllipticEst.Honest.honSliceDivCosLintegral
import Submission.Work.FTS.EllipticEst.Honest.aemeasurable_sliceSigmaLin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- **The `ρ`-norm of `Ψ/cos θ` is bounded by the `ρ`-norms of `Ψ` and of `∂_θΨ`.**

`∫⁻_z w(z)² ∫⁻_θ σ θ (Ψ(z,θ)/cos θ)² ≤ 100 (Y + X)` where `Y = ∫⁻_z w² ∫⁻_θ σ Ψ²` and
`X = ∫⁻_z w² ∫⁻_θ σ (∂_θΨ)²`, `σ θ = sin(2θ)^{-η}`.

Cheapest route: `Honest/honSliceDivCosLintegral.lean` (proved, clash-free) already gives the
*slicewise lintegral* form `∫⁻_θ σ(Ψ/cos)² ≤ 100(∫⁻_θ σΨ² + ∫⁻_θ σ(∂_θΨ)²)` for every
`Hon α F Ψ` and every `z > 0` (its route: `Honest/sliceBarSq2.lean` plus the bar limit of
`Honest/honestBarLim.lean`).  Multiplying by `ofReal ((w z)²) ≥ 0`, integrating over `Iz` and
using the monotonicity of the lintegral (`lintegral_mono_ae`), its additivity
(`lintegral_add_left`/`lintegral_add_right` on `ℝ≥0∞`-valued functions) and the fact that the
set `{z ∈ Iz : ¬ 0 < z}` is null, gives the statement with `C = 100`. -/
theorem honYcBound : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.Honest.Hon α F Ψ →
      (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ / Real.cos θ) ^ 2)))
        ≤ ENNReal.ofReal C *
          ((∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ) ^ 2)))
            + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                (Work.FTS.EllipticEst.AngSecond.sig θ * (Work.Spaces.pth Ψ z θ) ^ 2)))) := by
  refine ⟨100, by norm_num, ?_⟩
  intro α F Ψ h
  -- measurability of the radial weight
  have hwmeas : Measurable (fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2)) := by
    have hnum : Measurable (fun z : ℝ => (1 + z) ^ 2) :=
      (measurable_const.add measurable_id).pow_const 2
    have hden : Measurable (fun z : ℝ => z ^ 2) := measurable_id.pow_const 2
    have h1 : Measurable (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) :=
      (hnum.div hden).pow_const 2
    exact ENNReal.measurable_ofReal.comp h1
  have hR1meas : AEMeasurable (fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hwmeas.aemeasurable.mul (by
      simpa only [Work.FTS.EllipticEst.AngSecond.sig, Work.FTS.EllipticEst.sEta]
        using aemeasurable_sliceSigmaLin Ψ h.sm)
  -- the pointwise (in `z`) bound
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ / Real.cos θ) ^ 2))
        ≤ 100 * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ) ^ 2))
            + ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                (Work.FTS.EllipticEst.AngSecond.sig θ * (Work.Spaces.pth Ψ z θ) ^ 2))) := by
    intro z hzI
    have hz0 : (0 : ℝ) ≤ z := hzI
    rcases eq_or_lt_of_le hz0 with hz | hzpos
    · -- `z = 0`: the weight `w 0 = 0` kills both sides
      rw [← hz, Work.Spaces.w]
      simp
    · -- `z > 0`: the slicewise inequality, multiplied by `ofReal (w z ^ 2)`
      calc ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ / Real.cos θ) ^ 2))
          ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (100 * ((∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                    (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ) ^ 2))
                + (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                    (Work.FTS.EllipticEst.AngSecond.sig θ * (Work.Spaces.pth Ψ z θ) ^ 2)))) :=
            mul_le_mul_right (honSliceDivCosLintegral h hzpos) _
        _ = 100 * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
                (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                  (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ) ^ 2))
              + ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
                (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                  (Work.FTS.EllipticEst.AngSecond.sig θ * (Work.Spaces.pth Ψ z θ) ^ 2))) := by
            ring
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hmono := MeasureTheory.lintegral_mono_ae
    (MeasureTheory.ae_restrict_of_forall_mem (μ := volume) hIz hpt)
  have hkey : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ / Real.cos θ) ^ 2)))
      ≤ 100 * ((∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
            (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
              (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ) ^ 2)))
          + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
            (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
              (Work.FTS.EllipticEst.AngSecond.sig θ * (Work.Spaces.pth Ψ z θ) ^ 2)))) := by
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ / Real.cos θ) ^ 2)))
        ≤ ∫⁻ z in Work.Spaces.Iz, 100 * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ) ^ 2))
            + ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                (Work.FTS.EllipticEst.AngSecond.sig θ * (Work.Spaces.pth Ψ z θ) ^ 2))) := hmono
      _ = 100 * (∫⁻ z in Work.Spaces.Iz, (ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ) ^ 2))
            + ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                (Work.FTS.EllipticEst.AngSecond.sig θ * (Work.Spaces.pth Ψ z θ) ^ 2)))) :=
          MeasureTheory.lintegral_const_mul' 100 _ (by norm_num)
      _ = 100 * ((∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ) ^ 2)))
            + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                (Work.FTS.EllipticEst.AngSecond.sig θ * (Work.Spaces.pth Ψ z θ) ^ 2)))) := by
          rw [MeasureTheory.lintegral_add_left' hR1meas]
  rw [show ENNReal.ofReal (100 : ℝ) = (100 : ℝ≥0∞) from by norm_num]
  exact hkey

end Work.FTS.EllipticEst.Honest
