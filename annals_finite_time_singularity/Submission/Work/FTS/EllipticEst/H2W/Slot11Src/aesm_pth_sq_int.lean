import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Slot11Src

open MeasureTheory
open scoped Real Topology

/-!
## Almost everywhere strong measurability of `w(z)² ∫_θ (∂_θG z θ)² sin(2θ)^{2-γ}`

For a source `G` which is `C^∞` on the *open* quadrant `Q0 = (0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen`), the function

`z ↦ w(z)² · ∫_{Iθ} (∂_θG z θ)² · sin(2θ)^{2-γ(α)}`

is almost everywhere strongly measurable for the Lebesgue measure restricted to
`Iz = [0,∞)`.

The `θ`-integrand is continuous on `Q0`: the factor `(∂_θG)²` because `∂_θ` preserves
`C^∞` on the open quadrant (`SmoothOpen.pth`), and the weight `sin(2θ)^{2-γ}` because
`sin(2θ) ≠ 0` on `(0,π/2)` (an `rpow` with a positive base is continuous for *any* real
exponent).  So the product function is a.e. strongly measurable for the product of the
restricted measures (`Work.Spaces.aesm_of_continuousOn_Qd`), and integrating out the
`θ`-variable (`AEStronglyMeasurable.integral_prod_right'`) gives a.e. strong measurability
of the `z`-integral.  Multiplying by the continuous function `w²` (continuous on `Ioi 0`,
which is co-null in `Iz`) preserves this.
-/

/-- The weight `w` is continuous on the open half-line `(0,∞)`. -/
private theorem continuousOn_w : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
  show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi (0 : ℝ))
  exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
    (continuous_id.pow 2).continuousOn
    (fun z hz => pow_ne_zero 2 (ne_of_gt (by simpa using hz)))

theorem aesm_pth_sq_int (α : ℝ) {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth G z θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  -- The square of the angular derivative is continuous on the open quadrant.
  have hpth : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pth G p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hG.pth).continuousOn.pow 2
  -- The weight `sin(2θ)^{2-γ(α)}` is continuous on the open interval.
  have hφc : ContinuousOn (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    refine hsin.rpow_const (fun θ hθ => Or.inl ?_)
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.pth G p.1 p.2) ^ 2
        * Real.rpow (Real.sin (2 * p.2)) (2 - Work.Spaces.gam α))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hpth.mul (hφc.comp continuous_snd.continuousOn (fun p hp => hp.2))
  -- Hence it is a.e. strongly measurable for the product of the restricted measures ...
  have hprod : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.pth G p.1 p.2) ^ 2
        * Real.rpow (Real.sin (2 * p.2)) (2 - Work.Spaces.gam α))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- ... and integrating out the `θ`-variable preserves this.
  have hint : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth G z θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hprod
  -- The prefactor `w²` is continuous on `(0,∞)`, which is co-null in `Iz = [0,∞)`.
  have hw : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (continuousOn_w.pow 2).aestronglyMeasurable
      (μ := MeasureTheory.volume) measurableSet_Ioi
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))] at h
    exact h
  exact hw.mul hint

end Work.FTS.EllipticEst.H2W.Slot11Src
