import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Submission.Work.BoseBoxFock.SqrtKinDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKin.heatK_mass`

The heat kernel `heatK t z = (4πt)^{-3/2} exp(-‖z‖²/(4t))` of `∂_t = Δ` on `ℝ³` has total mass
`1`: for every `t > 0` and every `x`,

`∫ y, heatK t (x - y) = 1`.

This is the normalisation used when the heat pairing `kinMass g − kinHeat g t = ⅟₂·diffHeat g t`
is written as a convolution against a probability kernel.

Proof: translation/reflection invariance of Lebesgue measure on `ℝ³`
(`integral_sub_left_eq_self`) reduces the statement to `∫ z, heatK t z = 1`, which is the
elementary Gaussian integral `∫_z exp(-b‖z‖²) = (π/b)^{3/2}` with `b = 1/(4t)`, together with
`(4πt)^{-3/2}(4πt)^{3/2} = 1`.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseBoxFock.SqrtKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem heatK_mass {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin 3)) :
    ∫ y : EuclideanSpace ℝ (Fin 3), heatK t (x - y) = 1 := by
  -- translation/reflection invariance: `y ↦ x - y` preserves Lebesgue measure
  have hshift : ∫ y : ℝ³, heatK t (x - y) = ∫ y : ℝ³, heatK t y :=
    integral_sub_left_eq_self (fun z : ℝ³ => heatK t z) volume x
  rw [hshift]
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hfr : Module.finrank ℝ ℝ³ = 3 := by simp
  have hgauss : ∫ z : ℝ³, Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2)
      = (Real.pi / (1 / (4 * t))) ^ (3 / 2 : ℝ) := by
    have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℝ³) hb
    rw [hfr] at h
    simpa using h
  have hshape : ∀ z : ℝ³,
      heatK t z = (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2) := by
    intro z
    unfold heatK
    rw [show -(1 / (4 * t)) * ‖z‖ ^ 2 = -(‖z‖ ^ 2 / (4 * t)) by ring]
  calc ∫ z : ℝ³, heatK t z
      = (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
          * ∫ z : ℝ³, Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall hshape)
    _ = (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
          * (Real.pi / (1 / (4 * t))) ^ (3 / 2 : ℝ) := by rw [hgauss]
    _ = 1 := by
        have hdiv : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by field_simp
        rw [hdiv]
        have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
        rw [← Real.rpow_add hpos]
        norm_num

end Work.BoseBoxFock.SqrtKin
