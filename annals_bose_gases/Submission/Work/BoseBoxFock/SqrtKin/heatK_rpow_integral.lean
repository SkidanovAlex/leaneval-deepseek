import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SqrtKin.heatK_const_arith
import Submission.Work.BoseBoxFock.SqrtKin.inv_cube_exp_div
import Submission.Work.BoseBoxFock.SqrtKinDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKin.heatK_rpow_integral`

The `t`-integral of `t^{-3/2}` against the heat kernel of `ℝ³`:

`∫_0^∞ t^{-3/2} · (4πt)^{-3/2} e^{-‖z‖²/(4t)} dt = 2 / (π^{3/2} ‖z‖⁴)`   (`z ≠ 0`).

This is the third ingredient of the identity `sqrtKin_diffForm`: it is the radial
`t`-integral that converts the heat-regularised difference form into the Riesz kernel
`‖x - y‖^{-4}` (up to the constant combination `(2√π)^{-1}·⅟₂·2π^{-3/2} = (2π²)^{-1}`).

**Proof.** The pointwise factorisation

  `t^{-3/2} (4πt)^{-3/2} = (4π)^{-3/2} t^{-3}`   (`t > 0`)

(`heatK_rpow_factor` below) reduces the statement to the classical Mellin-type integral

  `∫_0^∞ t^{-3} e^{-c/t} dt = 1/c²`   (`c > 0`)

with `c = ‖z‖²/4`; this is the lemma `inv_cube_exp_div` (proved by the substitution
`t ↦ 1/t`, i.e. `MeasureTheory.integral_comp_rpow_Ioi` at exponent `-1`, followed by the
Gamma integral `Real.integral_rpow_mul_exp_neg_mul_Ioi` at `a = 2` and `Real.Gamma_two`).
Since `1/c² = 16/‖z‖⁴`, it remains only to combine the numeric constants:
`(4π)^{-3/2}·16/‖z‖⁴ = 2/(π^{3/2}‖z‖⁴)`, which is the lemma `heatK_const_arith`.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseBoxFock.SqrtKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Pointwise factorisation of the integrand.** For `t > 0`,
`t^{-3/2}·heatK t z = (4π)^{-3/2} · t^{-3} · e^{-((‖z‖²/4)/t)}`,
using `(4πt)^{-3/2} = (4π)^{-3/2} t^{-3/2}`, `t^{-3/2}·t^{-3/2} = t^{-3}` and
`‖z‖²/(4t) = (‖z‖²/4)/t`. -/
private lemma heatK_rpow_factor {t : ℝ} (ht : 0 < t) (z : ℝ³) :
    t ^ (-(3 : ℝ) / 2) * heatK t z
      = (4 * Real.pi) ^ (-(3 : ℝ) / 2)
          * (t ^ (-(3 : ℝ)) * Real.exp (-((‖z‖ ^ 2 / 4) / t))) := by
  unfold heatK
  have hsplit : (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
      = (4 * Real.pi) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * Real.pi) ht.le]
  rw [hsplit]
  have hexp : ‖z‖ ^ 2 / (4 * t) = (‖z‖ ^ 2 / 4) / t := by ring
  rw [hexp]
  have hpow : t ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) = t ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_add ht]
    norm_num
  calc t ^ (-(3 : ℝ) / 2) * ((4 * Real.pi) ^ (-(3 : ℝ) / 2)
          * t ^ (-(3 : ℝ) / 2) * Real.exp (-((‖z‖ ^ 2 / 4) / t)))
      = (4 * Real.pi) ^ (-(3 : ℝ) / 2)
          * ((t ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2))
              * Real.exp (-((‖z‖ ^ 2 / 4) / t))) := by ring
    _ = _ := by rw [hpow]

theorem heatK_rpow_integral {z : EuclideanSpace ℝ (Fin 3)} (hz : z ≠ 0) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * heatK t z
      = 2 / (Real.pi ^ (3 / 2 : ℝ) * ‖z‖ ^ 4) := by
  have hc : 0 < ‖z‖ ^ 2 / 4 := by
    have h : 0 < ‖z‖ := norm_pos_iff.mpr hz
    positivity
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => heatK_rpow_factor ht z),
    MeasureTheory.integral_const_mul, inv_cube_exp_div hc]
  exact heatK_const_arith ‖z‖

end Work.BoseBoxFock.SqrtKin
