import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB4.BoxChiScaling
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.realIP_thetaFun_thetaFun`

The sharp characteristic function `θ_Λ = 1_{Λ(ℓ)}` of the box `Λ(ℓ) = boxL ℓ`
(`Work.BoseB4.BoxChi`) is the condensate vector of FS's box problem.  Its norm is
`|Λ(ℓ)| = ℓ³`, i.e.

  `⟨θ_Λ, θ_Λ⟩ = ∫ Re(conj θ_Λ · θ_Λ) = volume Λ(ℓ) = ℓ³`,

which is exactly `Work.BoseB4.BoxData.realIP_thetaFun_thetaFun`.

The integrand `Re(conj θ x · θ x)` is the indicator function of `boxL ℓ` (the
values of `θ` are `0` and `1`), so the identity reduces to the computation of the
volume of the box, `Work.BoseB4.BoxData.volume_boxL`.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

namespace BoxData

variable (B : BoxData)

/-- The integrand of `⟨θ_Λ, θ_Λ⟩` is the indicator function of the box:
`Re(conj θ x · θ x) = 1_{boxL ℓ}(x)`. -/
lemma thetaFun_integrand_eq_indicator (ℓ : ℝ) :
    (fun x : EuclideanSpace ℝ (Fin 3) =>
        ((starRingEnd ℂ) (B.thetaFun ℓ x) * B.thetaFun ℓ x).re)
      = (B.boxL ℓ).indicator (1 : EuclideanSpace ℝ (Fin 3) → ℝ) := by
  funext x
  by_cases hx : x ∈ B.boxL ℓ
  · simp [BoxData.thetaFun_apply, hx]
  · simp [BoxData.thetaFun_apply, hx]

/-- The box of side `ℓ` has volume `ℓ³`, as a real number
(the `toReal` form of `Work.BoseB4.BoxData.volume_boxL`). -/
lemma volume_boxL_toReal {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume (B.boxL ℓ)).toReal = ℓ ^ 3 := by
  rw [B.volume_boxL hℓ, ENNReal.toReal_ofReal (by positivity)]

end BoxData

/-- **The norm of the condensate vector**: `⟨θ_Λ, θ_Λ⟩ = ℓ³`, the volume of the
box `Λ(ℓ)`. -/
theorem realIP_thetaFun_thetaFun (B : Work.BoseB4.BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    B.realIP (B.thetaFun ℓ) (B.thetaFun ℓ) = ℓ ^ 3 := by
  rw [BoxData.realIP_apply, B.thetaFun_integrand_eq_indicator ℓ,
    integral_indicator_one (B.boxL_measurableSet ℓ)]
  simp only [MeasureTheory.measureReal_def]
  exact B.volume_boxL_toReal hℓ

end Work.BoseB4
