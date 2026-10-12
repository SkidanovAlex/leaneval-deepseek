import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.WinAuxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.winAux_winW_integrable` — `winW` is integrable

`winW ℓ ψ = 1_{Λ(ℓ)}·|Q_Λψ|` with `Q_Λψ = Qfree ℓ 0 ψ = ψ − |Λ(ℓ)|⁻¹∫_{Λ(ℓ)}ψ`, the localised
mean-free state as a nonnegative weight (`WinAuxDefs`).  The point of this little module is that
`winW` is an *honest* `L¹`-weight: it is integrable for every smooth `ψ` and every `ℓ > 0`.

The proof is the obvious one: `winW ℓ ψ` is the indicator of the compact cube `Λ(ℓ) = acube ℓ` of
the continuous function `z ↦ |ψ z − c|`, `c = |Λ(ℓ)|⁻¹∫_{Λ(ℓ)}ψ`.  On the *compact* cube
`acube ℓ` every continuous function is integrable (`ContinuousOn.integrableOn_compact`, Lebesgue
measure being finite on compacta), and integrability over the cube is equivalent to integrability
of the indicator (`IntegrableOn.integrable_indicator`).  Note that `ℓ > 0` is used only through
the compactness of the cube.

The module also records the identity in the form in which it is consumed downstream,
`Work.BoseBoxFock.winW_eq_indicator_abs_sub_mean`, and the general (weight-free) statement
`Work.BoseBoxFock.integrable_indicator_abs_sub_of_contDiff`.
-/

noncomputable section

open MeasureTheory

open scoped Real

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **`winW ℓ ψ` is the indicator of the cube of the absolute deviation from the box mean**:
`winW ℓ ψ z = 1_{Λ(ℓ)}(z)·|ψ z − |Λ(ℓ)|⁻¹∫_{Λ(ℓ)}ψ|`. -/
lemma winW_eq_indicator_abs_sub_mean (ℓ : ℝ) (ψ : E3 → ℝ) (z : E3) :
    winW ℓ ψ z = (Submission.BoseGases.acube ℓ).indicator
      (fun z => |ψ z - (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.acube ℓ, ψ x|) z := by
  simp [Work.BoseBoxFock.winW, Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ,
    Work.BSKinetic.bsMean]

/-- **A general integrability statement**: the cube-indicator of the absolute deviation of a
continuous function from its cube mean is integrable.  (Only the *compactness* of the cube and
the finiteness of Lebesgue measure on compacta are used.) -/
lemma integrable_indicator_abs_sub_of_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : E3 → ℝ}
    (hψ : Continuous ψ) :
    MeasureTheory.Integrable ((Submission.BoseGases.acube ℓ).indicator
      (fun z => |ψ z - (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.acube ℓ, ψ x|)) :=
  (ContinuousOn.integrableOn_compact (μ := volume)
    (Submission.BoseGases.acube_compact hℓ)
    ((hψ.sub continuous_const).abs).continuousOn).integrable_indicator
      (Submission.BoseGases.acube_measurable ℓ)

theorem winAux_winW_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    MeasureTheory.Integrable (Work.BoseBoxFock.winW ℓ ψ) := by
  rw [funext (winW_eq_indicator_abs_sub_mean ℓ ψ)]
  exact integrable_indicator_abs_sub_of_contDiff hℓ hψ.continuous

end Work.BoseBoxFock
