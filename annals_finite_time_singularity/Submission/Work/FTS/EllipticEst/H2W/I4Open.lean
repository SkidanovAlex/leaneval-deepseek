import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.H2W.sliceI4Open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## The global `I₄` estimate out of the slicewise one

`sliceI4Open` (the honest, open-quadrant form of the `I₄`-term of Step 2 of `prop:H2`) gives,
for every `z > 0`,

  `∫_θ ∂_θ(tan θ Ψ) · ∂_θθΨ · w²σ - ∫_θ Ψ · ∂_θθΨ · w²σ ≤ (1-η)·∫_θ Ψ² · w²σ`,

so integrating in `z` (the three `IPMem` hypotheses make the three `z`-slice functions
integrable, and `w 0 = 0` makes `z = 0` harmless) gives the stated weighted `L²` inequality with
`C = 1 - η = 1/100`. -/
theorem I4Open : ∃ C : ℝ, 0 < C ∧ ∀ (Ψ : ℝ → ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
    (Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ)) →
    (Work.FTS.EllipticEst.AngSecond.IPMem Ψ (Work.Spaces.pthIter 2 Ψ)) →
    (Work.FTS.EllipticEst.AngSecond.IPMem Ψ Ψ) →
    (∀ z, 0 < z → MeasureTheory.IntegrableOn (fun θ => (Ψ z θ / Real.cos θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    (∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    (∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    (∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Real.sin θ) ^ 2
        * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    - Work.FTS.EllipticEst.AngSecond.IP Ψ (Work.Spaces.pthIter 2 Ψ)
        - C * Work.FTS.EllipticEst.AngSecond.IP Ψ Ψ
      ≤ - Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          (Work.Spaces.pthIter 2 Ψ) := by
  refine ⟨1 - Work.Spaces.eta, by rw [Work.Spaces.eta]; norm_num, ?_⟩
  intro Ψ hsm h0 hpi hM1 hM2 hM3 hB hBD hB2 hBD2
  set u : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ with hu
  set b : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hb
  set FA : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    u z θ * b z θ * AngSecond.w2 z * AngSecond.sig θ with hFA
  set FB : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    Ψ z θ * b z θ * AngSecond.w2 z * AngSecond.sig θ with hFB
  set FN : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    Ψ z θ * Ψ z θ * AngSecond.w2 z * AngSecond.sig θ with hFN
  -- the three `z`-slice functions are integrable, by the three `IPMem` hypotheses
  have hAint : IntegrableOn FA Work.Spaces.Iz := hM1.2
  have hBint : IntegrableOn FB Work.Spaces.Iz := hM2.2
  have hNint : IntegrableOn FN Work.Spaces.Iz := hM3.2
  have hGint : IntegrableOn (fun z => FB z + (1 - Work.Spaces.eta) * FN z) Work.Spaces.Iz :=
    hBint.add (hNint.const_mul _)
  -- the slicewise inequality, with the harmless point `z = 0` handled separately
  have hpoint : ∀ z ∈ Work.Spaces.Iz, FA z ≤ FB z + (1 - Work.Spaces.eta) * FN z := by
    intro z hz
    rcases eq_or_lt_of_le (show 0 ≤ z from hz) with hz0 | hzpos
    · subst hz0
      have hw0 : AngSecond.w2 0 = 0 := by rw [AngSecond.w2, Work.Spaces.w]; norm_num
      have hFA0 : FA 0 = 0 := by rw [hFA]; simp [hw0]
      have hFB0 : FB 0 = 0 := by rw [hFB]; simp [hw0]
      have hFN0 : FN 0 = 0 := by rw [hFN]; simp [hw0]
      rw [hFA0, hFB0, hFN0]; simp
    · have hsl := sliceI4Open Ψ hsm h0 hpi hzpos hM1 hM2 hM3
        (hB z hzpos) (hBD z hzpos) (hB2 z hzpos) (hBD2 z hzpos)
      have hsl' : FA z - FB z ≤ (1 - Work.Spaces.eta) * FN z := hsl
      linarith
  -- integrate the slicewise inequality in `z`
  have hmono : ∫ z in Work.Spaces.Iz, FA z
      ≤ ∫ z in Work.Spaces.Iz, (FB z + (1 - Work.Spaces.eta) * FN z) :=
    MeasureTheory.setIntegral_mono_on hAint hGint measurableSet_Ici (fun z hz => hpoint z hz)
  have hsplit : ∫ z in Work.Spaces.Iz, (FB z + (1 - Work.Spaces.eta) * FN z)
      = (∫ z in Work.Spaces.Iz, FB z)
        + (1 - Work.Spaces.eta) * (∫ z in Work.Spaces.Iz, FN z) := by
    rw [MeasureTheory.integral_add hBint (hNint.const_mul _), MeasureTheory.integral_const_mul]
  -- the pairings are the three `z`-integrals
  have hIP1 : AngSecond.IP
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ) = ∫ z in Work.Spaces.Iz, FA z := rfl
  have hIP2 : AngSecond.IP Ψ (Work.Spaces.pthIter 2 Ψ)
      = ∫ z in Work.Spaces.Iz, FB z := rfl
  have hIP3 : AngSecond.IP Ψ Ψ = ∫ z in Work.Spaces.Iz, FN z := rfl
  rw [hIP1, hIP2, hIP3]
  linarith

end

end Work.FTS.EllipticEst.H2W
